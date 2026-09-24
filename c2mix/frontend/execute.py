"""Component X: the executor (spec §5.5).

Control flow runs on concrete values, data stays symbolic. That is the whole idea of
D1: a loop whose trip count does not depend on the input unrolls by simply running it,
and an array element whose address is concrete becomes its own SSA value. What comes
out is a c2mix IR trace (§5.2) plus one snapshot per time point (§5.5).

Everything the executor cannot run this way is refused with a spec error code and the
source line, never approximated — see `ExecError` and A3.7.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field

from ..ir import ops
from ..ir.trace import CUT, ENTRY_POINT, EXIT_POINT, ObjectInfo, Point, Snapshot, Trace
from . import llparse as L

RUNTIME = {"c2mix_register", "c2mix_input", "c2mix_cut", "c2mix_done"}
IGNORED_INTRINSICS = ("@llvm.dbg.", "@llvm.lifetime.", "@llvm.assume", "@llvm.prefetch",
                      "@llvm.experimental.noalias")
VEXIT = "\0exit"

MAX_STEPS = 100_000_000
MAX_MERGE_DEPTH = 8


class ExecError(Exception):
    def __init__(self, code: str, message: str, line: int | None = None, ir_line: int = 0):
        super().__init__(f"{code}: {message}" +
                         (f" (source line {line})" if line else "") +
                         (f" [ir line {ir_line}]" if ir_line else ""))
        self.code, self.message, self.line, self.ir_line = code, message, line, ir_line


class _Done(Exception):
    """c2mix_done(): the program's exit point."""


# ------------------------------------------------------------------ runtime values
@dataclass(frozen=True)
class Const:
    """A concrete bit pattern of a known width. Constant-only operations stay here and
    never reach the trace (§5.5: they are folded on the spot)."""
    bits: int
    width: int

    def signed_value(self) -> int:
        return self.bits - (1 << self.width) if self.bits >> (self.width - 1) else self.bits

    def value(self, signed: bool) -> int:
        return self.signed_value() if signed else self.bits


@dataclass(frozen=True)
class Ptr:
    obj: int
    off: int


@dataclass
class Obj:
    """A memory object: an alloca, a global, or a registered object (§5.5)."""
    kind: str
    name: str
    ty: L.Type
    layout: list                          # [(byte offset, scalar type)]
    cells: list                           # runtime values, None when never written
    index: dict = field(default_factory=dict)      # byte offset -> cell number
    reg: str | None = None                # registered name
    signed: bool | None = None

    @property
    def size(self) -> int:
        return self.ty.size


def flatten(ty: L.Type, base: int = 0) -> list:
    if ty.kind in ("int", "ptr"):
        return [(base, ty)]
    if ty.kind == "array":
        sz = ty.elem.size
        return [c for i in range(ty.count) for c in flatten(ty.elem, base + i * sz)]
    if ty.kind == "struct":
        out, off = [], base
        for f in ty.fields:
            a = 1 if ty.packed else f.align
            off = (off + a - 1) // a * a
            out += flatten(f, off)
            off += f.size
        return out
    raise ExecError("E-UNSUPPORTED", f"no layout for type {ty}")


def make_obj(kind: str, name: str, ty: L.Type) -> Obj:
    layout = flatten(ty)
    o = Obj(kind, name, ty, layout, [None] * len(layout))
    o.index = {off: i for i, (off, _) in enumerate(layout)}
    return o


# ------------------------------------------------------------------------- the CFG
class CFG:
    """Successors and immediate post-dominators; the merge rule of §5.5 needs the
    latter to know where two symbolic branches come back together."""

    def __init__(self, fn: L.Function):
        self.fn = fn
        self.blocks = {b.label: b for b in fn.blocks}
        self.entry = fn.blocks[0].label
        self.succ = {}
        for b in fn.blocks:
            term = b.instrs[-1] if b.instrs else None
            if term is None or term.op not in L.TERMINATORS:
                raise ExecError("E-UNSUPPORTED", f"{fn.name}: block {b.label} has no terminator")
            if term.op == "br":
                self.succ[b.label] = [key(l) for l in term.labels]
            elif term.op == "switch":
                self.succ[b.label] = [key(term.labels[0])] + [key(l) for _, _, l in term.cases]
            else:
                self.succ[b.label] = [VEXIT]
        self.succ[VEXIT] = []
        self.ipdom = self._postdom()
        self._reach = {}

    def _postdom(self) -> dict:
        nodes = list(self.succ)
        pd = {n: set(nodes) for n in nodes}
        pd[VEXIT] = {VEXIT}
        changed = True
        while changed:
            changed = False
            for n in nodes:
                if n == VEXIT:
                    continue
                acc = set(nodes)
                for s in self.succ[n]:
                    acc &= pd[s]
                acc = acc | {n}
                if acc != pd[n]:
                    pd[n], changed = acc, True
        ipdom = {}
        for n in nodes:
            cands = pd[n] - {n}
            # Every other candidate post-dominates the immediate one, so it is the
            # candidate with the largest post-dominator set.
            ipdom[n] = max(cands, key=lambda c: len(pd[c])) if cands else None
        return ipdom

    def reaches(self, src: str, dst: str, avoid: str | None = None) -> bool:
        """Is `dst` reachable from `src` without passing through `avoid`? With `avoid`
        set to the join point this is what tells a loop test apart from an `if`: only
        a loop lets an arm arrive back at the branch without reaching the join."""
        memo = self._reach.get((src, dst, avoid))
        if memo is not None:
            return memo
        seen, stack = set(), [src]
        found = False
        while stack:
            n = stack.pop()
            if n == dst:
                found = True
                break
            if n in seen or n == avoid:
                continue
            seen.add(n)
            stack += self.succ.get(n, [])
        self._reach[(src, dst, avoid)] = found
        return found


def key(label: str) -> str:
    return label.lstrip("%")


# ---------------------------------------------------------------------- call frames
@dataclass
class Frame:
    fn: L.Function
    env: dict
    dbg_signed: dict
    prev: str = ""


DBG_VALUE_RE = re.compile(r"(%[-a-zA-Z$._0-9]+)")


def dbg_signedness(fn: L.Function, dbg: L.DebugInfo) -> dict:
    """§5.1 rule 3: a named C local's signedness, taken from its DIBasicType."""
    out = {}
    for blk in fn.blocks:
        for ins in blk.instrs:
            if ins.op != "call" or not (ins.callee or "").startswith("@llvm.dbg.value"):
                continue
            args = ins.call_args
            if len(args) < 2 or args[0].raw is None:
                continue
            m = DBG_VALUE_RE.search(args[0].raw or "")
            ref = (args[1].raw or "").split()[-1]
            if not m or not ref.startswith("!"):
                continue
            s = dbg.var_signed(ref)
            if s is not None:
                out.setdefault(m.group(1), s)
    return out


# -------------------------------------------------------------------- the executor
class Executor:
    def __init__(self, mod: L.Module, entry: str, max_steps: int = MAX_STEPS,
                 max_merge_depth: int = MAX_MERGE_DEPTH, main: str = "c2mix_body"):
        self.mod = mod
        self.entry = entry.lstrip("@")
        self.main = main.lstrip("@")
        self.max_steps = max_steps
        self.max_merge_depth = max_merge_depth
        self.dbg = L.DebugInfo(mod)
        L.attach_lines(mod)

        self.b = ops.Builder()
        self.objs: list[Obj] = []
        self.globals: dict[str, int] = {}
        self.registered: dict[str, int] = {}        # registered name -> object id
        self.info: dict[str, ObjectInfo] = {}
        self.snapshots: list[Snapshot] = []
        self.cut_counts: dict[str, int] = {}
        self.steps = 0
        self.merges = 0
        self.max_depth_seen = 0
        self.entry_taken = False
        self.stack: list[str] = []
        self.origins: dict[str, dict] = {}
        self._cfgs: dict[str, CFG] = {}
        self._cut_ban = 0                           # >0 while inside a merged branch

    # -------------------------------------------------------------- object helpers
    def new_obj(self, kind: str, name: str, ty: L.Type) -> int:
        self.objs.append(make_obj(kind, name, ty))
        return len(self.objs) - 1

    def cfg(self, fn: L.Function) -> CFG:
        if fn.name not in self._cfgs:
            self._cfgs[fn.name] = CFG(fn)
        return self._cfgs[fn.name]

    def _init_globals(self) -> None:
        for g in self.mod.globals:
            if g.name in self.globals:
                continue
            oid = self.new_obj("global", g.name, g.ty)
            self.globals[g.name] = oid
            self._init_cells(self.objs[oid], g.ty, g.init, 0)

    def _init_cells(self, obj: Obj, ty: L.Type, init, base: int) -> None:
        if init is None or isinstance(init, L.Special) and init.word == "zeroinitializer":
            for off, cty in flatten(ty, base):
                if cty.kind == "int":
                    obj.cells[obj.index[off]] = Const(0, cty.bits)
            return
        if isinstance(init, L.StringLit):
            data = decode_c_string(init.text)
            for i, byte in enumerate(data):
                obj.cells[obj.index[base + i]] = Const(byte, 8)
            return
        if isinstance(init, L.Aggregate):
            off = base
            for i, (ety, val) in enumerate(init.elems):
                if ty.kind == "array":
                    off = base + i * ty.elem.size
                self._init_cells(obj, ety, val, off)
                if ty.kind == "struct":
                    a = 1 if ty.packed else ety.align
                    off = (off + a - 1) // a * a + ety.size
            return
        if isinstance(init, L.IntLit) and ty.kind == "int":
            obj.cells[obj.index[base]] = Const(init.value & ((1 << ty.bits) - 1), ty.bits)
            return
        if isinstance(init, L.Special):
            return                                   # undef / null: leave uninitialised
        raise ExecError("E-UNSUPPORTED", f"initialiser {init} for {obj.name}")

    # ----------------------------------------------------------------------- driver
    def run(self) -> Trace:
        self._init_globals()
        main = self.mod.function(self.main)
        if main is None:
            raise ExecError("E-UNSUPPORTED", f"no function @{self.main} in the module")
        try:
            self.call(main, [])
        except _Done:
            pass
        else:
            raise ExecError("E-UNSUPPORTED", "the program returned without calling c2mix_done()")
        return Trace(self.b.build(), dict(self.info), list(self.snapshots),
                     dict(self.origins))

    def call(self, fn: L.Function, args: list):
        if fn.name in self.stack:
            raise ExecError("E-RECURSION", f"{fn.name} calls itself", ir_line=fn.ir_line)
        if len(fn.blocks) == 0:
            raise ExecError("E-EXTERNAL-CALL", f"{fn.name} has no body", ir_line=fn.ir_line)
        env = {}
        for p, a in zip(fn.params, args):
            if p.name:
                env[p.name] = a
                if isinstance(a, ops.Value) and "signext" in p.attrs and not a.signed:
                    env[p.name] = a.as_signed(True)
                elif isinstance(a, ops.Value) and "zeroext" in p.attrs and a.signed:
                    env[p.name] = a.as_signed(False)
        fr = Frame(fn, env, dbg_signedness(fn, self.dbg))
        self.stack.append(fn.name)
        try:
            cfg = self.cfg(fn)
            kind, payload, _ = self.region(fr, cfg, cfg.entry, frozenset(), 0)
            if kind != "ret":
                raise ExecError("E-UNSUPPORTED", f"{fn.name}: fell out of the function")
            return payload
        finally:
            self.stack.pop()

    # ------------------------------------------------------------------- the region
    def region(self, fr: Frame, cfg: CFG, start: str, stop: frozenset, depth: int,
               seed: dict | None = None):
        """Run blocks from `start`, stopping before any block in `stop`.
        Returns ('ret', value, None) or ('stop', label, previous label)."""
        cur, prev = start, fr.prev
        pending = seed or {}
        while True:
            if cur in stop:
                return "stop", cur, prev
            blk = cfg.blocks.get(cur)
            if blk is None:
                raise ExecError("E-UNSUPPORTED", f"{fr.fn.name}: no block {cur}")
            i = 0
            for ins in blk.instrs:
                if ins.op != "phi":
                    break
                i += 1
                if ins.result in pending:
                    fr.env[ins.result] = pending.pop(ins.result)
                else:
                    fr.env[ins.result] = self.phi_value(fr, ins, prev)
            pending = {}
            for ins in blk.instrs[i:]:
                self.steps += 1
                before = len(self.b.prog.instrs)
                if self.steps > self.max_steps:
                    raise ExecError("E-UNBOUNDED", f"more than {self.max_steps} steps",
                                    ins.line, ins.ir_line)
                if ins.op in L.TERMINATORS:
                    out = self.terminator(fr, cfg, blk, ins, stop, depth)
                    if out[0] == "ret":
                        return out
                    if out[0] == "stop":
                        return out
                    cur, prev, pending = out[1], out[2], out[3]
                    self._note_origin(before, ins, fr)
                    break
                self.step(fr, ins)
                self._note_origin(before, ins, fr)

    def _note_origin(self, before: int, ins: L.Instr, fr: Frame) -> None:
        """Every IR value this instruction produced points back at it (§7.5)."""
        for i in self.b.prog.instrs[before:]:
            if i.result is not None:
                self.origins.setdefault(i.result.name, {
                    "llvm": ins.result or ins.op, "line": ins.line,
                    "function": fr.fn.name.lstrip("@")})

    def terminator(self, fr: Frame, cfg: CFG, blk: L.Block, ins: L.Instr,
                   stop: frozenset, depth: int):
        if ins.op == "ret":
            val = self.operand(fr, ins.args[0], ins.ty, ins) if ins.args else None
            return "ret", val, None
        if ins.op == "unreachable":
            raise ExecError("E-UNREACHABLE", "reached an `unreachable` instruction",
                            ins.line, ins.ir_line)
        if ins.op == "br" and not ins.args:
            return "go", key(ins.labels[0]), blk.label, {}
        cond = self.operand(fr, ins.args[0], ins.ty, ins) if ins.args else None
        if ins.op == "switch":
            if isinstance(cond, Const):
                for _, val, lbl in ins.cases:
                    if val.value & ((1 << ins.ty.bits) - 1) == cond.bits:
                        return "go", key(lbl), blk.label, {}
                return "go", key(ins.labels[0]), blk.label, {}
            raise ExecError("E-SYMBOLIC-BRANCH", "switch on an input-dependent value",
                            ins.line, ins.ir_line)
        if isinstance(cond, Const):
            return "go", key(ins.labels[0 if cond.bits else 1]), blk.label, {}
        return self.merge(fr, cfg, blk, ins, cond, stop, depth)

    # -------------------------------------------------------------------- merging
    def merge(self, fr: Frame, cfg: CFG, blk: L.Block, ins: L.Instr, cond,
              stop: frozenset, depth: int):
        """An input-dependent `br` (§5.5): run both arms to the immediate
        post-dominator and join them with `ite`."""
        t, f = key(ins.labels[0]), key(ins.labels[1])
        join = cfg.ipdom[blk.label]
        if join is None:
            raise ExecError("E-SYMBOLIC-BRANCH", "the two arms never come back together",
                            ins.line, ins.ir_line)
        if cfg.reaches(t, blk.label, join) or cfg.reaches(f, blk.label, join):
            raise ExecError("E-SYMBOLIC-LOOP", "a loop test depends on the input",
                            ins.line, ins.ir_line)
        if depth + 1 > self.max_merge_depth:
            raise ExecError("E-SYMBOLIC-BRANCH",
                            f"merge nesting deeper than {self.max_merge_depth}",
                            ins.line, ins.ir_line)
        self.merges += 1
        self.max_depth_seen = max(self.max_depth_seen, depth + 1)

        saved_env, saved_mem = dict(fr.env), self.save_memory()
        self._cut_ban += 1
        try:
            fr.prev = blk.label
            res_t = self.region(fr, cfg, t, frozenset({join}), depth + 1)
            env_t, mem_t = dict(fr.env), self.save_memory()
            fr.env = dict(saved_env)
            self.restore_memory(saved_mem)
            fr.prev = blk.label
            res_f = self.region(fr, cfg, f, frozenset({join}), depth + 1)
            env_f, mem_f = dict(fr.env), self.save_memory()
        finally:
            self._cut_ban -= 1
        fr.env = dict(saved_env)
        self.restore_memory(mem_f)
        self.join_memory(cond, mem_t, mem_f, ins)

        if res_t[0] == "ret" or res_f[0] == "ret":
            if res_t[0] != res_f[0]:
                raise ExecError("E-SYMBOLIC-BRANCH", "only one arm returns",
                                ins.line, ins.ir_line)
            return "ret", self.select(cond, res_t[1], res_f[1], ins), None
        if join == VEXIT:
            raise ExecError("E-SYMBOLIC-BRANCH", "the arms do not join inside the function",
                            ins.line, ins.ir_line)
        pending = {}
        for phi in cfg.blocks[join].instrs:
            if phi.op != "phi":
                break
            a = self.phi_value(Frame(fr.fn, env_t, fr.dbg_signed), phi, res_t[2])
            b = self.phi_value(Frame(fr.fn, env_f, fr.dbg_signed), phi, res_f[2])
            pending[phi.result] = self.select(cond, a, b, phi)
        return "go", join, blk.label, pending

    def save_memory(self) -> list:
        return [(len(self.objs), None)] + [(o, list(o.cells)) for o in self.objs]

    def restore_memory(self, saved: list) -> None:
        n = saved[0][0]
        del self.objs[n:]
        for obj, cells in saved[1:]:
            obj.cells = list(cells)

    def join_memory(self, cond, mem_t: list, mem_f: list, ins: L.Instr) -> None:
        for (obj, cells_t), (_, cells_f) in zip(mem_t[1:], mem_f[1:]):
            for i, (a, b) in enumerate(zip(cells_t, cells_f)):
                if same_value(a, b):
                    obj.cells[i] = a
                elif a is None or b is None:
                    obj.cells[i] = None          # written on one arm only: undefined after
                else:
                    obj.cells[i] = self.select(cond, a, b, ins)

    def select(self, cond, a, b, ins: L.Instr):
        if same_value(a, b):
            return a
        if a is None or b is None:
            raise ExecError("E-UNINIT", "one arm of a merge has no value",
                            ins.line, ins.ir_line)
        if isinstance(a, Ptr) or isinstance(b, Ptr):
            raise ExecError("E-UNSUPPORTED", "a merge would produce a symbolic pointer",
                            ins.line, ins.ir_line)
        width = a.width if isinstance(a, (Const, ops.Value)) else b.width
        signed = self.pick_signed(None, [a, b], ins, None)
        c = self.as_value(cond, 1, False, ins)
        va = self.as_value(a, width, signed, ins)
        vb = self.as_value(b, width, signed, ins)
        return self.b.ite(c, va, vb)

    # ------------------------------------------------------------------- operands
    def operand(self, fr: Frame, val, ty: L.Type | None, ins: L.Instr | None):
        if isinstance(val, L.Reg):
            if val.name not in fr.env:
                raise ExecError("E-UNINIT", f"{val.name} has no value",
                                ins.line if ins else None, ins.ir_line if ins else 0)
            v = fr.env[val.name]
            if v is None:
                raise ExecError("E-UNINIT", f"{val.name} is undef",
                                ins.line if ins else None, ins.ir_line if ins else 0)
            return v
        if isinstance(val, L.IntLit):
            w = ty.bits if ty is not None and ty.kind == "int" else 64
            return Const(val.value & ((1 << w) - 1), w)
        if isinstance(val, L.GlobalRef):
            if val.name not in self.globals:
                raise ExecError("E-EXTERNAL-CALL", f"{val.name} is not defined in the module",
                                ins.line if ins else None, ins.ir_line if ins else 0)
            return Ptr(self.globals[val.name], 0)
        if isinstance(val, L.Special):
            if val.word == "zeroinitializer" and ty is not None and ty.kind == "int":
                return Const(0, ty.bits)
            if val.word == "null":
                return Ptr(-1, 0)
            raise ExecError("E-UNINIT", f"operand is {val.word}",
                            ins.line if ins else None, ins.ir_line if ins else 0)
        if isinstance(val, L.ConstExpr):
            return self.const_expr(fr, val, ins)
        raise ExecError("E-UNSUPPORTED", f"operand {val}",
                        ins.line if ins else None, ins.ir_line if ins else 0)

    def const_expr(self, fr: Frame, expr: L.ConstExpr, ins):
        lx = L.Lexer(expr.raw)
        head = lx.next()
        while lx.peek() in L.IGNORED_FLAGS:
            lx.next()
        if head != "getelementptr":
            raise ExecError("E-UNSUPPORTED", f"constant expression {expr.raw}",
                            ins.line if ins else None, ins.ir_line if ins else 0)
        lx.expect("(")
        ty = L.parse_type(lx)
        lx.expect(",")
        L.parse_type(lx)
        base = self.operand(fr, L.parse_value(lx), None, ins)
        idx = []
        while lx.eat(","):
            L.parse_type(lx)
            idx.append(self.operand(fr, L.parse_value(lx), L.int_type(64), ins))
        return self.gep(base, ty, idx, ins)

    def as_value(self, x, width: int, signed: bool, ins: L.Instr | None) -> ops.Value:
        if isinstance(x, Const):
            if x.width != width:
                raise ExecError("E-UNSUPPORTED", f"width {x.width} used as {width}",
                                ins.line if ins else None, ins.ir_line if ins else 0)
            return self.b.const(x.value(signed), width, signed)
        if isinstance(x, ops.Value):
            if x.width != width:
                raise ExecError("E-UNSUPPORTED", f"{x} used at width {width}",
                                ins.line if ins else None, ins.ir_line if ins else 0)
            return x.as_signed(signed)
        raise ExecError("E-UNSUPPORTED", f"{x!r} is not an integer value",
                        ins.line if ins else None, ins.ir_line if ins else 0)

    def pick_signed(self, fr: Frame | None, vals, ins: L.Instr, forced: bool | None = None):
        """§5.1: the producing operation first, then debug info, then the operands."""
        if forced is not None:
            return forced
        if fr is not None and ins.result and ins.result in fr.dbg_signed:
            return fr.dbg_signed[ins.result]
        s = {v.signed for v in vals if isinstance(v, ops.Value)}
        return s.pop() if len(s) == 1 else False

    def phi_value(self, fr: Frame, ins: L.Instr, prev: str):
        for val, lbl in ins.incoming:
            if key(lbl) == key(prev):
                return self.operand(fr, val, ins.ty, ins)
        raise ExecError("E-UNSUPPORTED", f"phi has no entry for block {prev}",
                        ins.line, ins.ir_line)

    # --------------------------------------------------------------------- memory
    def gep(self, base, ty: L.Type, idx: list, ins) -> Ptr:
        if not isinstance(base, Ptr):
            raise ExecError("E-UNSUPPORTED", "getelementptr on a non-pointer",
                            ins.line if ins else None, ins.ir_line if ins else 0)
        for i in idx:
            if not isinstance(i, Const):
                raise ExecError("E-DYN-INDEX", "an index depends on the input",
                                ins.line if ins else None, ins.ir_line if ins else 0)
        off = base.off + idx[0].signed_value() * ty.size if idx else base.off
        cur = ty
        for i in idx[1:]:
            n = i.signed_value()
            if cur.kind == "array":
                off += n * cur.elem.size
                cur = cur.elem
            elif cur.kind == "struct":
                pos, o = 0, 0
                for f in cur.fields[:n]:
                    a = 1 if cur.packed else f.align
                    o = (o + a - 1) // a * a + f.size
                fld = cur.fields[n]
                a = 1 if cur.packed else fld.align
                off += (o + a - 1) // a * a
                cur = fld
            else:
                raise ExecError("E-UNSUPPORTED", f"cannot index into {cur}",
                                ins.line if ins else None, ins.ir_line if ins else 0)
        return Ptr(base.obj, off)

    def cell(self, p, ty: L.Type, ins) -> tuple[Obj, int]:
        if not isinstance(p, Ptr) or not 0 <= p.obj < len(self.objs):
            raise ExecError("E-UNINIT", "access through an invalid pointer",
                            ins.line, ins.ir_line)
        obj = self.objs[p.obj]
        i = obj.index.get(p.off)
        if i is None:
            raise ExecError("E-MIXED-ACCESS",
                            f"offset {p.off} in {obj.name} is not the start of an element",
                            ins.line, ins.ir_line)
        if obj.layout[i][1] != ty:
            raise ExecError("E-MIXED-ACCESS",
                            f"{obj.name}[{i}] is {obj.layout[i][1]}, accessed as {ty}",
                            ins.line, ins.ir_line)
        return obj, i

    # ---------------------------------------------------------------------- steps
    def step(self, fr: Frame, ins: L.Instr) -> None:
        op = ins.op
        bad = set(ins.flags) & L.POISON_FLAGS
        if bad:
            raise ExecError("E-POISON-FLAG", f"{op} carries {', '.join(sorted(bad))}",
                            ins.line, ins.ir_line)
        if op == "alloca":
            fr.env[ins.result] = Ptr(self.new_obj("alloca", ins.result, ins.ty), 0)
        elif op == "load":
            p = self.operand(fr, ins.args[0], L.PTR, ins)
            obj, i = self.cell(p, ins.ty, ins)
            v = obj.cells[i]
            if v is None:
                raise ExecError("E-UNINIT", f"{obj.name}[{i}] was never written",
                                ins.line, ins.ir_line)
            if obj.signed is not None and isinstance(v, ops.Value):
                v = v.as_signed(obj.signed)
            fr.env[ins.result] = v
        elif op == "store":
            val = self.operand(fr, ins.args[0], ins.ty, ins)
            p = self.operand(fr, ins.args[1], L.PTR, ins)
            obj, i = self.cell(p, ins.ty, ins)
            obj.cells[i] = val
        elif op == "getelementptr":
            base = self.operand(fr, ins.args[0], L.PTR, ins)
            idx = [self.operand(fr, a, t, ins) for a, t in zip(ins.args[1:], ins.cases)]
            fr.env[ins.result] = self.gep(base, ins.ty, idx, ins)
        elif op in L.BINOPS:
            fr.env[ins.result] = self.binop(fr, ins)
        elif op in L.CASTS:
            fr.env[ins.result] = self.cast(fr, ins)
        elif op == "icmp":
            fr.env[ins.result] = self.icmp(fr, ins)
        elif op == "select":
            c = self.operand(fr, ins.args[0], ins.ty2, ins)
            a = self.operand(fr, ins.args[1], ins.ty, ins)
            b = self.operand(fr, ins.args[2], ins.ty, ins)
            fr.env[ins.result] = a if isinstance(c, Const) and c.bits else \
                b if isinstance(c, Const) else self.select(c, a, b, ins)
        elif op == "call":
            self.do_call(fr, ins)
        else:
            raise ExecError("E-UNSUPPORTED", f"instruction {op}", ins.line, ins.ir_line)

    def binop(self, fr: Frame, ins: L.Instr):
        w = ins.ty.bits
        a = self.operand(fr, ins.args[0], ins.ty, ins)
        b = self.operand(fr, ins.args[1], ins.ty, ins)
        op = ins.op
        m = (1 << w) - 1
        if op in ("shl", "lshr", "ashr"):
            if not isinstance(b, Const):
                raise ExecError("E-VAR-SHIFT", "the shift amount depends on the input",
                                ins.line, ins.ir_line)
            k = b.bits
            if k >= w:
                raise ExecError("E-POISON-FLAG", f"shift by {k} at width {w} is poison",
                                ins.line, ins.ir_line)
            if isinstance(a, Const):
                if op == "shl":
                    return Const((a.bits << k) & m, w)
                if op == "lshr":
                    return Const(a.bits >> k, w)
                return Const((a.signed_value() >> k) & m, w)
            if op == "shl":
                signed = self.pick_signed(fr, [a], ins)
                return self.b.shl(self.as_value(a, w, signed, ins), k)
            if op == "ashr":
                return self.b.ashr(self.as_value(a, w, True, ins), k)
            return self.b.lshr(self.as_value(a, w, False, ins), k)
        if isinstance(a, Const) and isinstance(b, Const):
            x, y = a.bits, b.bits
            val = {"add": x + y, "sub": x - y, "mul": x * y,
                   "and": x & y, "or": x | y, "xor": x ^ y}[op]
            return Const(val & m, w)
        if op == "xor" and isinstance(b, Const) and b.bits == m:              # §5.2
            signed = self.pick_signed(fr, [a], ins)
            return self.b.not_(self.as_value(a, w, signed, ins))
        if op == "sub" and isinstance(a, Const) and a.bits == 0:
            signed = self.pick_signed(fr, [b], ins)
            return self.b.neg(self.as_value(b, w, signed, ins))
        signed = self.pick_signed(fr, [a, b], ins)
        return self.b.binop(op, self.as_value(a, w, signed, ins),
                            self.as_value(b, w, signed, ins))

    def cast(self, fr: Frame, ins: L.Instr):
        a = self.operand(fr, ins.args[0], ins.ty, ins)
        src, dst = ins.ty.bits, ins.ty2.bits
        if isinstance(a, Const):
            if ins.op == "trunc":
                return Const(a.bits & ((1 << dst) - 1), dst)
            if ins.op == "zext":
                return Const(a.bits, dst)
            return Const(a.signed_value() & ((1 << dst) - 1), dst)
        if ins.op == "trunc":
            signed = self.pick_signed(fr, [a], ins)
            return self.b.extract(self.as_value(a, src, a.signed, ins), dst - 1, 0,
                                  signed=signed)
        if ins.op == "zext":
            return self.b.zext(self.as_value(a, src, False, ins), dst)
        return self.b.sext(self.as_value(a, src, True, ins), dst)

    def icmp(self, fr: Frame, ins: L.Instr):
        w = ins.ty.bits
        a = self.operand(fr, ins.args[0], ins.ty, ins)
        b = self.operand(fr, ins.args[1], ins.ty, ins)
        pred = ins.pred
        signed = pred in ops.SIGNED_PREDS
        if isinstance(a, Const) and isinstance(b, Const):
            x, y = a.value(signed), b.value(signed)
            out = {"eq": x == y, "ne": x != y, "ult": a.bits < b.bits, "ule": a.bits <= b.bits,
                   "ugt": a.bits > b.bits, "uge": a.bits >= b.bits, "slt": x < y,
                   "sle": x <= y, "sgt": x > y, "sge": x >= y}[pred]
            return Const(int(out), 1)
        if pred in ("eq", "ne"):
            signed = self.pick_signed(fr, [a, b], ins)
        return self.b.cmp(pred, self.as_value(a, w, signed, ins),
                          self.as_value(b, w, signed, ins))

    # ---------------------------------------------------------------------- calls
    def do_call(self, fr: Frame, ins: L.Instr) -> None:
        name = ins.callee
        if name.startswith(IGNORED_INTRINSICS):
            return
        if name.startswith("@llvm.memcpy") or name.startswith("@llvm.memmove"):
            return self.do_memcpy(fr, ins)
        if name.startswith("@llvm.memset"):
            return self.do_memset(fr, ins)
        if name.startswith("@llvm."):
            raise ExecError("E-UNSUPPORTED", f"intrinsic {name}", ins.line, ins.ir_line)
        bare = name.lstrip("@")
        if bare in RUNTIME:
            return self.do_runtime(fr, ins, bare)
        fn = self.mod.function(name)
        if fn is None or not fn.blocks:
            raise ExecError("E-EXTERNAL-CALL", f"{name} has no definition in the module",
                            ins.line, ins.ir_line)
        if fn.name in self.stack:                # report it at the call, not at the define
            raise ExecError("E-RECURSION", f"{name} calls itself", ins.line, ins.ir_line)
        args = [self.operand(fr, a.value, a.ty, ins) for a in ins.call_args if a.ty is not None]
        if fn.name.lstrip("@") == self.entry and not self.entry_taken:
            self.entry_taken = True
            self.snapshot(ENTRY_POINT)
        out = self.call(fn, args)
        if ins.result is not None:
            if out is None:
                raise ExecError("E-UNINIT", f"{name} returned no value", ins.line, ins.ir_line)
            if isinstance(out, ops.Value):
                if "signext" in ins.flags and not out.signed:
                    out = out.as_signed(True)
                elif "zeroext" in ins.flags and out.signed:
                    out = out.as_signed(False)
            fr.env[ins.result] = out

    def do_memcpy(self, fr: Frame, ins: L.Instr) -> None:
        args = [a for a in ins.call_args if a.ty is not None]
        dst = self.operand(fr, args[0].value, L.PTR, ins)
        src = self.operand(fr, args[1].value, L.PTR, ins)
        n = self.operand(fr, args[2].value, args[2].ty, ins)
        if not isinstance(n, Const):
            raise ExecError("E-DYN-INDEX", "memcpy with a symbolic length", ins.line, ins.ir_line)
        sobj = self.objs[src.obj]
        for off, cty in sobj.layout:
            if not src.off <= off < src.off + n.bits:
                continue
            dobj, di = self.cell(Ptr(dst.obj, dst.off + off - src.off), cty, ins)
            dobj.cells[di] = sobj.cells[sobj.index[off]]

    def do_memset(self, fr: Frame, ins: L.Instr) -> None:
        args = [a for a in ins.call_args if a.ty is not None]
        dst = self.operand(fr, args[0].value, L.PTR, ins)
        byte = self.operand(fr, args[1].value, args[1].ty, ins)
        n = self.operand(fr, args[2].value, args[2].ty, ins)
        if not isinstance(n, Const) or not isinstance(byte, Const):
            raise ExecError("E-DYN-INDEX", "memset with a symbolic length or value",
                            ins.line, ins.ir_line)
        obj = self.objs[dst.obj]
        for off, cty in obj.layout:
            if not dst.off <= off < dst.off + n.bits:
                continue
            if cty.kind != "int":
                raise ExecError("E-MIXED-ACCESS", "memset over a non-integer element",
                                ins.line, ins.ir_line)
            pattern = int(str(format(byte.bits, "02x")) * (cty.bits // 8), 16) if cty.bits >= 8 \
                else byte.bits & ((1 << cty.bits) - 1)
            obj.cells[obj.index[off]] = Const(pattern, cty.bits)

    def do_runtime(self, fr: Frame, ins: L.Instr, which: str) -> None:
        args = [self.operand(fr, a.value, a.ty, ins) for a in ins.call_args if a.ty is not None]
        if which == "c2mix_done":
            self.snapshot(EXIT_POINT)
            raise _Done()
        if which == "c2mix_cut":
            if self._cut_ban:
                raise ExecError("E-SYMBOLIC-BRANCH", "c2mix_cut() inside a merged branch",
                                ins.line, ins.ir_line)
            if not isinstance(args[0], Const):
                raise ExecError("E-UNSUPPORTED", "c2mix_cut() with a symbolic tag",
                                ins.line, ins.ir_line)
            tag = str(args[0].signed_value())
            k = self.cut_counts.get(tag, 0) + 1
            self.cut_counts[tag] = k
            self.b.marker(f"{tag}#{k}")
            self.snapshot(Point(CUT, tag, k))
            return
        name = self.read_string(args[0], ins)
        if which == "c2mix_register":
            return self.do_register(name, args, ins)
        if name not in self.registered:
            raise ExecError("E-BAD-REGISTER", f"c2mix_input({name!r}): not registered",
                            ins.line, ins.ir_line)
        info = self.info[name]
        obj = self.objs[self.registered[name]]
        pad = len(str(info.count - 1))
        for i in range(info.count):
            vn = f"{name}_{i:0{pad}d}" if info.count > 1 else name
            obj.cells[i] = self.b.input(vn, info.width, info.signed)
            self.origins[vn] = {"object": name, "index": i}

    def do_register(self, name: str, args: list, ins: L.Instr) -> None:
        p, count, elem, signed = args[1], args[2], args[3], args[4]
        if not isinstance(p, Ptr) or p.off != 0:
            raise ExecError("E-BAD-REGISTER", f"c2mix_register({name!r}) needs an object start",
                            ins.line, ins.ir_line)
        if not all(isinstance(x, Const) for x in (count, elem, signed)):
            raise ExecError("E-BAD-REGISTER", f"c2mix_register({name!r}) needs constant shape",
                            ins.line, ins.ir_line)
        if name in self.registered:
            raise ExecError("E-BAD-REGISTER", f"{name!r} is registered twice",
                            ins.line, ins.ir_line)
        n, width = count.bits, elem.bits * 8
        obj = self.objs[p.obj]
        if len(obj.layout) < n:
            raise ExecError("E-BAD-REGISTER", f"{name!r}: {obj.name} holds {len(obj.layout)} "
                            f"elements, not {n}", ins.line, ins.ir_line)
        for i in range(n):
            off, cty = obj.layout[i]
            if cty.kind != "int" or cty.bits != width or off != i * elem.bits:
                raise ExecError("E-MIXED-ACCESS", f"{name!r}[{i}] is {cty}, not i{width}",
                                ins.line, ins.ir_line)
        obj.reg, obj.signed = name, bool(signed.bits)
        self.registered[name] = p.obj
        self.info[name] = ObjectInfo(name, n, width, bool(signed.bits))

    def read_string(self, p, ins) -> str:
        if not isinstance(p, Ptr):
            raise ExecError("E-BAD-REGISTER", "a name argument is not a pointer",
                            ins.line, ins.ir_line)
        obj = self.objs[p.obj]
        out = bytearray()
        off = p.off
        while off in obj.index:
            c = obj.cells[obj.index[off]]
            if not isinstance(c, Const) or c.width != 8:
                raise ExecError("E-BAD-REGISTER", "a name argument is not a literal string",
                                ins.line, ins.ir_line)
            if c.bits == 0:
                return out.decode()
            out.append(c.bits)
            off += 1
        raise ExecError("E-BAD-REGISTER", "unterminated name string", ins.line, ins.ir_line)

    # ------------------------------------------------------------------ snapshots
    def snapshot(self, point: Point) -> None:
        values = {}
        for name, info in self.info.items():
            obj = self.objs[self.registered[name]]
            for i in range(info.count):
                v = obj.cells[i]
                if v is None:
                    continue
                values[(name, i)] = self.as_value(v, info.width, info.signed, None)
        self.snapshots.append(Snapshot(point, values, len(self.b.prog.instrs)))


def same_value(a, b) -> bool:
    if a is None or b is None:
        return a is b
    if isinstance(a, ops.Value) and isinstance(b, ops.Value):
        return a.name == b.name and a.signed == b.signed
    return a == b


ESCAPE = re.compile(r"\\([0-9A-Fa-f]{2})")


def decode_c_string(text: str) -> bytes:
    out = bytearray()
    i = 0
    while i < len(text):
        m = ESCAPE.match(text, i)
        if m:
            out.append(int(m.group(1), 16))
            i = m.end()
        else:
            out.append(ord(text[i]))
            i += 1
    return bytes(out)


def resolve_entry(mod: L.Module, entry: str) -> str:
    """Targets name the C function; namespacing macros may have renamed the symbol."""
    entry = entry.lstrip("@")
    names = [f.name.lstrip("@") for f in mod.functions]
    if entry in names:
        return entry
    tail = [n for n in names if n.endswith("_" + entry)]
    if len(tail) == 1:
        return tail[0]
    raise ExecError("E-UNSUPPORTED",
                    f"no function {entry} in the module" if not tail else
                    f"{entry} is ambiguous: {', '.join(tail)}")


def execute(mod: L.Module, entry: str, max_steps: int = MAX_STEPS,
            max_merge_depth: int = MAX_MERGE_DEPTH, main: str = "c2mix_body"):
    """Run the module and return (trace, statistics)."""
    ex = Executor(mod, resolve_entry(mod, entry), max_steps, max_merge_depth, main)
    trace = ex.run()
    stats = {"steps": ex.steps, "merges": ex.merges, "merge_depth": ex.max_depth_seen,
             "objects": len(ex.objs), "cuts": len(trace.cuts()),
             "instructions": len(trace.prog.instrs), "inputs": len(trace.prog.inputs)}
    return trace, stats
