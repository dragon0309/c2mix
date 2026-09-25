"""Proving many small claims about one segment's range model (the engine behind §6.4).

A segment's range model can hold thousands of statements — a whole NTT layer — while a
hint candidate is usually about a single butterfly. Sending the whole model with every
candidate made hint discovery the slowest step of a build by far. Three things keep
it cheap:

  * slicing: a claim is sent with its cone of influence only — the definitions of the
    symbols it mentions, transitively, and every other statement or premise that touches
    one of them. Leaving assumptions out can only lose proofs, never invent one, so a
    claim proved from the slice holds in the whole model. The slice loses nothing
    either: a symbol outside the cone is defined once, from other symbols, and nothing
    else constrains it, so it can always take the value its definition gives.
  * deepening: most claims are local — the low limb of a Montgomery step is zero
    whatever the multiplier was — but the full cone of a value late in a multi-limb
    multiplication holds every 64×64 product before it, and z3 bit-blasts all of them.
    So a claim is first tried on a cone cut off a few definitions back, the symbols
    beyond left free; only the claims that fail there are retried deeper, and finally
    on the full cone — if that cone is of a size z3 can be expected to finish; a claim
    that needs all of a very large cone is given up, which only costs a hint. A
    shallower slice is still a subset of the model, so a proof there is a proof. `lo64(x + lo64(x·(2⁶⁴−1))) = 0` takes z3 0.02 s with x free, and
    does not finish in minutes with x's own definition chain attached.
  * batching: the sliced queries go to a few z3 processes, separated by `(reset)`, each
    query with its own resource limit, and each answer tagged so that an error in one
    query cannot shift the answers of the others.

The limit is z3's `rlimit`, not its `timeout`, for two reasons. A timeout is not checked
while z3 bit-blasts a large multiplier, so a "2 s" query was seen running for minutes;
and a timeout depends on how busy the machine is, so two builds could find different
hints and G8 would fail. The resource counter stops those queries and gives the same
answer every time. RLIMIT_PER_SECOND converts the budgets below, which are written in
seconds of an unloaded z3 4.8.12, into resource units.
"""
from __future__ import annotations

import os
import subprocess
from concurrent.futures import ThreadPoolExecutor

from ..mixfmt.writer import to_str

CHUNK = 256                       # queries per z3 process
DEPTHS = (4, 8, 16, None)         # cone depths tried in turn; None is the full cone
SHALLOW_TIMEOUT = 2.0             # seconds per query below the full cone
MAX_FULL_CONE = 400               # statements; beyond this the full cone is not tried
RLIMIT_PER_SECOND = 2_000_000     # z3 4.8.12: ~2M resource units per second of solving


def _symbols(term, known: dict) -> set[str]:
    out, stack = set(), [term]
    while stack:
        t = stack.pop()
        if isinstance(t, str):
            if t in known:
                out.add(t)
        elif isinstance(t, list):
            stack.extend(t)
    return out


class RangeModel:
    """The segment's QF_BV model — premises plus BV statements — indexed for slicing."""

    def __init__(self, seg, premises):
        self.sorts = {n: s for n, s in seg.decls.items()
                      if isinstance(s, list) and s[:2] == ["_", "BitVec"]}
        self.text: list[str] = []
        self.syms: list[set[str]] = []
        self.defs: dict[str, list[int]] = {}
        self.touch: dict[str, list[int]] = {}
        self.depth_of: dict[str, int | None] = {}    # proved claim -> cone depth used
        for t in premises:
            self._add(t, defines=None)
        for t in seg.bv:
            if isinstance(t, list) and t[0] == "=" and isinstance(t[1], str):
                if t[1] not in seg.decls:
                    continue
                if seg.decls.get(t[1]) == "Int":
                    continue                     # Int alias definitions are not QF_BV
                defines = t[1] if t[1] not in self.defs else None
                self._add(t, defines)
            else:
                self._add(t, defines=None)

    def _add(self, term, defines: str | None) -> None:
        idx = len(self.text)
        self.text.append(to_str(["assert", term]))
        syms = _symbols(term, self.sorts)
        self.syms.append(syms)
        if defines is not None:
            self.defs[defines] = [idx]       # a definition does not constrain its inputs,
            return                           # so it is reached only through what it defines
        for s in syms:                       # a constraint ties all of its symbols
            self.touch.setdefault(s, []).append(idx)

    def cone(self, claim, depth: int | None = None) -> tuple[list[str], list[int]]:
        """(symbols, statement indices) the claim depends on. With a depth, only
        statements reached within that many steps from the claim are kept; symbols
        first reached at the last step are declared but left free."""
        seen: set[str] = set()
        stmts: set[int] = set()
        frontier = sorted(_symbols(claim, self.sorts))
        level = 0
        while frontier:
            seen.update(frontier)
            if depth is not None and level >= depth:
                break
            nxt: set[str] = set()
            for s in frontier:
                for idx in self.defs.get(s, []) + self.touch.get(s, []):
                    if idx not in stmts:
                        stmts.add(idx)
                        nxt |= self.syms[idx]
            frontier = sorted(nxt - seen)
            level += 1
        return sorted(seen), sorted(stmts)

    def query(self, claim, depth: int | None = None) -> str:
        """A self-contained QF_BV script asking z3 to refute ¬claim over the slice."""
        names, stmts = self.cone(claim, depth)
        lines = ["(set-logic QF_BV)"]
        lines += [to_str(["declare-const", n, self.sorts[n]]) for n in names]
        lines += [self.text[i] for i in stmts]
        lines += [to_str(["assert", ["not", claim]]), "(check-sat)"]
        return "\n".join(lines) + "\n"


def prove_all(model: RangeModel, claims: list, z3_bin: str, timeout: float,
              jobs: int | None = None, depths=DEPTHS) -> list[bool]:
    """For each claim: did z3 prove it from the model? Unknown, timeout and error all
    count as not proved. Each claim is tried at the depths in turn (see above); the
    depth that worked is kept in `model.depth_of`, so the range VC can re-prove the
    same claim on the same slice."""
    results = [False] * len(claims)
    todo = list(range(len(claims)))
    for depth in depths:
        if not todo:
            break
        # a cut-off cone that already is the whole cone gains nothing from a retry, so
        # it gets the full timeout now; the others only a short one
        if depth is None:
            todo = [i for i in todo if len(model.cone(claims[i])[1]) <= MAX_FULL_CONE]
        full = {i for i in todo
                if depth is None or model.cone(claims[i], depth) == model.cone(claims[i])}
        limits = [timeout if i in full else min(timeout, SHALLOW_TIMEOUT) for i in todo]
        got = _solve([model.query(claims[i], depth) for i in todo], z3_bin, limits, jobs)
        left = []
        for i, ok in zip(todo, got):
            if ok:
                results[i] = True
                model.depth_of[_key(claims[i])] = depth
            elif i not in full:
                left.append(i)
        todo = left
    return results


def _key(claim) -> str:
    return to_str(claim)


def _solve(queries: list[str], z3_bin: str, timeouts: list[float],
           jobs: int | None = None) -> list[bool]:
    if not queries:
        return []
    jobs = max(1, jobs or min(8, os.cpu_count() or 1))
    size = max(1, min(CHUNK, -(-len(queries) // jobs)))   # every worker gets a share
    chunks = [list(range(i, min(i + size, len(queries))))
              for i in range(0, len(queries), size)]
    jobs = min(jobs, len(chunks))
    results = [False] * len(queries)

    def run(chunk: list[int]) -> None:
        script = "".join(f"(reset)\n(set-option :rlimit "
                         f"{int(timeouts[i] * RLIMIT_PER_SECOND)})\n"
                         f"{queries[i]}(echo \"@{i}\")\n" for i in chunk)
        try:                                  # the wall clock is only a backstop
            p = subprocess.run([z3_bin, "-in", "-smt2"], input=script, capture_output=True,
                               text=True, timeout=5 * sum(timeouts[i] for i in chunk) + 120)
        except subprocess.TimeoutExpired:
            return
        last, error = None, False
        for line in p.stdout.splitlines():
            line = line.strip()
            if line in ("sat", "unsat", "unknown"):
                last = line
            elif line.startswith("(error"):
                error = True
            elif line.startswith("@"):
                results[int(line[1:])] = last == "unsat" and not error
                last, error = None, False

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        list(pool.map(run, chunks))
    return results
