"""Lint for mix files: format contract M1–M10 (spec §7.3), in two profiles.

strict   : every rule is an error (except TRIVIAL-GOAL, which M6 allows) — c2mix output (G1).
consumer : only what extend_z3 cannot read or reads wrongly is an error; the rest
           are warnings — golden and other external corpora (A0.1).

Rule documentation: docs/lint-rules.md. Keep the two in sync.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path

from .prelude import POLY_CONSTRUCTORS, POLY_PREDICATES, SUPPORTED_PREDICATES
from .reader import (SECTION_COMMENTS, Command, Comment, MixFile, ParseError,
                     parse)

E, W = "E", "W"


@dataclass(frozen=True)
class Rule:
    code: str
    ref: str
    consumer: str
    strict: str
    summary: str


RULES = {r.code: r for r in [
    Rule("SET-LOGIC", "M1", E, E, "exactly one (set-logic ALL), alone on the first line mentioning (set-logic, before any declaration or assertion"),
    Rule("POLY-DECL", "M2", E, E, "no Poly datatype, no declaration of eqP/eqmodP*/Poly constructors, no declare-datatype(s)"),
    Rule("POLY-SORT", "M3", E, E, "the only Poly sort is (Poly Int)"),
    Rule("PRED", "M3", E, E, "Poly predicates are eqP/eqmodP1/eqmodP2 with the right arity; Poly constructors have the right arity"),
    Rule("PVAR", "M4", E, E, "PVar takes a string literal"),
    Rule("INDET-BV", "M4", W, E, "an indeterminate is encoded as a 1-bit bit-vector raised to a power"),
    Rule("BV2INT", "M5", W, E, "bv2int is used (z3 reads it as unsigned; use an Int alias)"),
    Rule("PCONST-ATOM", "M5", W, E, "PConst argument is not atomic (numeral, (- n), (bv2nat v), Int symbol)"),
    Rule("GOAL", "M6", E, E, "the postcondition section holds exactly one (assert (not ...))"),
    Rule("TRIVIAL-GOAL", "M6", W, W, "the goal is trivially true"),
    Rule("SYMBOL", "M7", W, E, "symbols match [A-Za-z_][A-Za-z0-9_]* and are not |quoted|"),
    Rule("CONST-FORMAT", "M8", W, E, "constant spelling: #x when the width is a multiple of 4, else #b; Int in decimal, negatives as (- n)"),
    Rule("SECTIONS", "M10", E, E, "the five section comments appear once each, in order, verbatim (incl. trailing space)"),
    Rule("DECL", "consumer", E, E, "every symbol is declared exactly once"),
    Rule("DECL-ORDER", "§7.3", W, E, "declarations are sorted by name"),
    Rule("LAYOUT", "§7.3", W, E, "file layout: header, what each section may contain, goal wrapped in (not (and ...)), no extra comments"),
    Rule("ALIAS", "§6.1", W, E, "each Int alias s__v has exactly one correct two's-complement definition in the range section"),
    Rule("PARSE", "consumer", E, E, "z3 parses the file with the extend_z3 prelude injected (only with --z3)"),
]}

PROFILES = ("strict", "consumer")

_SYMBOL_OK = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
_NUMERAL = re.compile(r"^\d+$")
_NEG_NUMERAL = re.compile(r"^-\d+$")
_DECIMAL = re.compile(r"^\d+\.\d+$")
_HEX = re.compile(r"^#x[0-9A-Fa-f]+$")
_BIN = re.compile(r"^#b[01]+$")
_ALIAS = re.compile(r"^s__(.+)$")

BUILTINS = {
    "true", "false", "and", "or", "not", "=>", "xor", "=", "distinct", "ite",
    "+", "-", "*", "div", "mod", "abs", "<=", "<", ">=", ">",
    "concat", "bvnot", "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvcomp",
    "bvneg", "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod",
    "bvshl", "bvlshr", "bvashr", "bvult", "bvule", "bvugt", "bvuge",
    "bvslt", "bvsle", "bvsgt", "bvsge", "bv2nat", "bv2int",
} | set(POLY_CONSTRUCTORS) | set(POLY_PREDICATES)
BINDERS = {"let", "forall", "exists"}
PRELUDE_NAMES = {"Poly"} | set(POLY_CONSTRUCTORS) | set(POLY_PREDICATES)
DECL_HEADS = {"declare-const", "declare-fun", "define-fun"}
HEADER = ["(set-info :smt-lib-version 2.0)", "(set-logic ALL)"]


@dataclass
class Diag:
    code: str
    severity: str
    line: int | None
    message: str
    path: str = ""

    @property
    def tag(self) -> str:
        return f"{self.severity}-{self.code}"

    def render(self) -> str:
        loc = f"{self.path}:{self.line}" if self.line else self.path
        return f"{loc}: {self.tag} {self.message}"


def _bv_width(sort) -> int | None:
    if isinstance(sort, list) and len(sort) == 3 and sort[:2] == ["_", "BitVec"] and _NUMERAL.match(sort[2]):
        return int(sort[2])
    return None


def _is_trivial(x) -> bool:
    if x == "true":
        return True
    return isinstance(x, list) and x[:1] == ["and"] and all(_is_trivial(a) for a in x[1:])


def _alias_def(v: str, w: int) -> list:
    return ["-", ["bv2nat", v], ["*", str(2 ** w), ["bv2nat", [["_", "extract", str(w - 1), str(w - 1)], v]]]]


class _Linter:
    def __init__(self, mix: MixFile, raw: str | None):
        self.mix = mix
        self.raw = raw
        self.found: list[tuple[str, int | None, str]] = []
        self._seen: set[tuple[str, int | None, str]] = set()
        self.decls: dict[str, tuple[object, int]] = {}   # name -> (sort, line)

    def add(self, code: str, line: int | None, msg: str, key: str | None = None):
        k = (code, line, key if key is not None else msg)
        if k not in self._seen:
            self._seen.add(k)
            self.found.append((code, line, msg))

    # -------------------------------------------------------------- M1 / M2 (raw text)
    def check_set_logic(self):
        cmds = self.mix.commands()
        sl = [c for c in cmds if c.head == "set-logic"]
        if not sl:
            self.add("SET-LOGIC", None, "no (set-logic ...) command")
            return
        for c in sl[1:]:
            self.add("SET-LOGIC", c.line, "more than one set-logic command")
        c = sl[0]
        if c.sexpr != ["set-logic", "ALL"]:
            self.add("SET-LOGIC", c.line, f"logic must be ALL, got {c.sexpr[1:]}")
        first = next((c2 for c2 in cmds if c2.head in DECL_HEADS | {"assert"}), None)
        if first is not None and first.line < c.line:
            self.add("SET-LOGIC", first.line, "declaration or assertion before set-logic")
        if self.raw is not None:
            # extend_z3 inserts the prelude after the line holding the first "(set-logic".
            pos = self.raw.find("(set-logic")
            ln = self.raw.count("\n", 0, pos) + 1
            line_text = self.raw.splitlines()[ln - 1]
            if ln != c.line or line_text.strip() != "(set-logic ALL)":
                self.add("SET-LOGIC", ln, "the first line containing '(set-logic' must be exactly "
                         "'(set-logic ALL)' (extend_z3 injects its prelude after that line)")

    def check_poly_decl(self):
        if self.raw is not None:
            if "(declare-datatype Poly" in self.raw or ("(declare-datatypes" in self.raw and "Poly" in self.raw):
                self.add("POLY-DECL", None, "file text matches extend_z3's 'Poly already declared' test; "
                         "its prelude will not be injected")
        for c in self.mix.commands():
            if _poly_decl(c):
                what = c.head if c.head not in DECL_HEADS else f"redeclaration of prelude name {c.sexpr[1]}"
                self.add("POLY-DECL", c.line, f"{what} is not allowed")

    # -------------------------------------------------------------- declarations
    def collect_decls(self):
        for c in self.mix.commands():
            if c.head not in DECL_HEADS:
                continue
            s = c.sexpr
            if len(s) < 3 or not isinstance(s[1], str):
                self.add("DECL", c.line, f"malformed {c.head}")
                continue
            name = s[1]
            if c.head == "declare-const":
                sort, argsorts = s[2], []
            elif c.head == "declare-fun" and len(s) == 4 and isinstance(s[2], list):
                sort, argsorts = s[3], s[2]
            elif c.head == "define-fun" and len(s) == 5 and isinstance(s[2], list):
                sort, argsorts = s[3], [a[1] for a in s[2] if isinstance(a, list) and len(a) == 2]
            else:
                self.add("DECL", c.line, f"malformed {c.head}")
                continue
            if name in self.decls:
                self.add("DECL", c.line, f"{name} declared again (first at line {self.decls[name][1]})")
            elif name not in PRELUDE_NAMES:
                self.decls[name] = (sort, c.line)
            if name.startswith("|") or not _SYMBOL_OK.match(name):
                self.add("SYMBOL", c.line, f"symbol {name} does not match [A-Za-z_][A-Za-z0-9_]*")
            for so in [sort, *argsorts]:
                self.check_sort(so, c.line)

    def check_sort(self, sort, line):
        stack = [sort]
        while stack:
            s = stack.pop()
            if isinstance(s, list):
                if s[:1] == ["Poly"] and s != ["Poly", "Int"]:
                    self.add("POLY-SORT", line, f"sort ({' '.join(map(str, s))}) — only (Poly Int) is allowed")
                stack.extend(x for x in s if isinstance(x, list))
            elif s == "Poly":
                self.add("POLY-SORT", line, "bare sort Poly — only (Poly Int) is allowed")

    # -------------------------------------------------------------- terms
    def check_terms(self):
        undeclared: dict[str, int] = {}
        for c in self.mix.commands():
            if c.head == "assert" and len(c.sexpr) == 2:
                self.walk(c.sexpr[1], c.line, undeclared)
            elif c.head == "assert":
                self.add("LAYOUT", c.line, "assert takes exactly one term")
            elif c.head == "define-fun" and len(c.sexpr) == 5 and isinstance(c.sexpr[2], list):
                params = frozenset(a[0] for a in c.sexpr[2] if isinstance(a, list) and a)
                self.walk(c.sexpr[4], c.line, undeclared, params)
        for name, line in undeclared.items():
            self.add("DECL", line, f"symbol {name} is used but not declared")

    def check_atom(self, a: str, line: int, bound, undeclared):
        if a.startswith('"') or a.startswith(":"):
            return
        if _NUMERAL.match(a):
            if len(a) > 1 and a[0] == "0":
                self.add("CONST-FORMAT", line, f"numeral {a} has leading zeros")
            return
        if _HEX.match(a):
            return
        if _BIN.match(a):
            if (len(a) - 2) % 4 == 0:
                self.add("CONST-FORMAT", line, f"{a[:20]}… has width {len(a) - 2}, a multiple of 4: write #x", key=a)
            return
        if _NEG_NUMERAL.match(a):
            self.add("CONST-FORMAT", line, f"negative Int written as {a}: write (- {a[1:]})", key=a)
            return
        if _DECIMAL.match(a):
            self.add("CONST-FORMAT", line, f"decimal literal {a}", key=a)
            return
        if a.startswith("|"):
            self.add("SYMBOL", line, f"quoted symbol {a}", key=a)
        if a in bound or a in BUILTINS or a in self.decls:
            return
        undeclared.setdefault(a, line)

    def walk(self, term, line: int, undeclared, bound=frozenset()):
        stack = [(term, bound)]
        while stack:
            node, bnd = stack.pop()
            if isinstance(node, str):
                self.check_atom(node, line, bnd, undeclared)
                continue
            if not node:
                self.add("LAYOUT", line, "empty list ()")
                continue
            head = node[0]
            if isinstance(head, list) and head[:1] == ["_"]:
                self.check_indexed(head, line)          # ((_ extract i j) x)
                stack.extend((x, bnd) for x in node[1:])
                continue
            if head == "_":
                self.check_indexed(node, line)
                continue
            if head in BINDERS and len(node) == 3 and isinstance(node[1], list):
                names = frozenset(b[0] for b in node[1] if isinstance(b, list) and b and isinstance(b[0], str))
                if head == "let":
                    stack.extend((b[1], bnd) for b in node[1] if isinstance(b, list) and len(b) == 2)
                stack.append((node[2], bnd | names))
                continue
            if head == "!":
                stack.append((node[1], bnd))
                continue
            if isinstance(head, str):
                self.check_app(head, node, line)
            stack.extend((x, bnd) for x in node)

    def check_indexed(self, node, line):
        if len(node) >= 2 and isinstance(node[1], str) and re.match(r"^bv\d+$", node[1]):
            self.add("CONST-FORMAT", line, f"(_ {node[1]} …) literal: write #x/#b", key=node[1])

    def check_app(self, head: str, node: list, line: int):
        nargs = len(node) - 1
        if head in POLY_PREDICATES:
            if head not in SUPPORTED_PREDICATES:
                self.add("PRED", line, f"{head} has no compiled handling in extend_z3 (at most 2 moduli)", key=head)
            elif nargs != POLY_PREDICATES[head]:
                self.add("PRED", line, f"{head} takes {POLY_PREDICATES[head]} arguments, got {nargs}", key=head)
        elif head in POLY_CONSTRUCTORS:
            if nargs != POLY_CONSTRUCTORS[head]:
                self.add("PRED", line, f"{head} takes {POLY_CONSTRUCTORS[head]} arguments, got {nargs}", key=head)
                return
            if head == "PVar" and not (isinstance(node[1], str) and node[1].startswith('"')):
                self.add("PVAR", line, "PVar argument must be a string literal")
            elif head == "PConst":
                self.check_pconst(node[1], line)
            elif head == "PPow":
                self.check_ppow(node, line)
        elif head == "bv2int":
            self.add("BV2INT", line, "bv2int is read as unsigned by z3; use an Int alias s__v", key="")

    def check_pconst(self, arg, line):
        if isinstance(arg, str):
            if _NUMERAL.match(arg):
                return
            if self.decls.get(arg, (None,))[0] == "Int":
                return
        elif len(arg) == 2 and arg[0] == "-" and isinstance(arg[1], str) and _NUMERAL.match(arg[1]):
            return
        elif len(arg) == 2 and arg[0] == "bv2nat" and isinstance(arg[1], str):
            return
        elif len(arg) == 2 and arg[0] == "bv2int":
            return                                    # reported as BV2INT
        self.add("PCONST-ATOM", line, "PConst argument is not atomic", key="")

    def check_ppow(self, node, line):
        base, k = node[1], node[2]
        if (isinstance(base, list) and len(base) == 2 and base[0] == "PConst"
                and isinstance(base[1], list) and len(base[1]) == 2
                and base[1][0] in ("bv2nat", "bv2int") and isinstance(base[1][1], str)
                and isinstance(k, str) and _NUMERAL.match(k) and int(k) >= 2):
            v = base[1][1]
            sort, dline = self.decls.get(v, (None, line))
            if _bv_width(sort) == 1:
                self.add("INDET-BV", dline, f"{v} is (_ BitVec 1) but raised to a power: an indeterminate "
                         "must be (PVar \"…\") (with a 1-bit value, v^k = v)", key=v)

    # -------------------------------------------------------------- sections
    def check_sections(self) -> dict | None:
        secs = self.mix.sections()
        if secs is not None:
            return secs
        texts = [it.text for it in self.mix.items if isinstance(it, Comment)]
        for want in SECTION_COMMENTS:
            n = texts.count(want)
            if n == 0:
                near = [t for t in texts if t.rstrip() == want.rstrip()]
                hint = f" (found {near[0]!r}: whitespace differs)" if near else ""
                self.add("SECTIONS", None, f"missing section comment {want!r}{hint}")
            elif n > 1:
                self.add("SECTIONS", None, f"section comment {want!r} appears {n} times")
        present = [t for t in texts if t in SECTION_COMMENTS]
        if len(set(present)) == len(present) == len(SECTION_COMMENTS) and present != list(SECTION_COMMENTS):
            self.add("SECTIONS", None, "section comments are out of order")
        return None

    def check_goal(self, secs):
        post = [it for it in secs["post"] if isinstance(it, Command)]
        if len(post) != 1:
            self.add("GOAL", post[1].line if len(post) > 1 else None,
                     f"postcondition section must hold exactly one assert, has {len(post)} commands")
            return
        c = post[0]
        s = c.sexpr
        if not (c.head == "assert" and len(s) == 2 and isinstance(s[1], list)
                and len(s[1]) == 2 and s[1][0] == "not"):
            self.add("GOAL", c.line, "goal must be (assert (not ...))")
            return
        x = s[1][1]
        if _is_trivial(x):
            canon = x == ["and", "true", "true"]
            self.add("TRIVIAL-GOAL", c.line, "trivial goal" + ("" if canon else
                     "; M6 spells it (assert (not (and true true)))"))
        elif not (isinstance(x, list) and x[:1] == ["and"]):
            self.add("LAYOUT", c.line, "goal is not wrapped in (not (and ...))")

    def check_layout(self, secs):
        # The set-logic command itself is SET-LOGIC's business; here only its neighbours.
        header = [it for it in secs["header"]
                  if not (isinstance(it, Command) and it.head == "set-logic")]
        got = [(it.text if isinstance(it, Comment) else _flat(it.sexpr)) for it in header]
        if got != HEADER[:1]:
            self.add("LAYOUT", header[0].line if header else None,
                     f"header must be exactly {HEADER}")
        for it in self.mix.items:
            if isinstance(it, Comment) and it.text not in SECTION_COMMENTS:
                self.add("LAYOUT", it.line, "comment other than the five section comments")
        for it in self.mix.inner_comments:
            self.add("LAYOUT", it.line, "comment inside a command")
        for it in secs["decl"]:
            if isinstance(it, Command) and _poly_decl(it):
                continue                                   # reported by POLY-DECL
            if isinstance(it, Command) and it.head != "declare-const":
                self.add("LAYOUT", it.line, f"declaration section holds {it.head or it.sexpr}, only declare-const is allowed")
        for name in ("range", "alg"):
            for it in secs[name]:
                if isinstance(it, Command) and it.head != "assert":
                    self.add("LAYOUT", it.line, f"{name} section holds {it.head or it.sexpr}, only assert is allowed")
        for it in secs["range"]:
            if isinstance(it, Command) and it.head == "assert" and _mentions_poly(it.sexpr):
                self.add("LAYOUT", it.line, "range section assert uses Poly terms")
        chk = [_flat(it.sexpr) for it in secs["check"] if isinstance(it, Command)]
        if chk != ["(check-sat)", "(exit)"]:
            self.add("LAYOUT", secs["check"][0].line if secs["check"] else None,
                     "check section must be exactly (check-sat) (exit)")

    def check_decl_order(self, secs):
        names = [(it.sexpr[1], it.line) for it in secs["decl"]
                 if isinstance(it, Command) and it.head == "declare-const" and len(it.sexpr) > 1]
        for (a, _), (b, line) in zip(names, names[1:]):
            if not a < b:
                self.add("DECL-ORDER", line, f"declarations not sorted by name ({b} after {a})")
                return

    def check_alias(self, secs):
        range_lines = {it.line for it in secs["range"] if isinstance(it, Command)}
        defs: dict[str, list[tuple[object, int]]] = {}
        for c in self.mix.commands():
            s = c.sexpr
            if (c.head == "assert" and len(s) == 2 and isinstance(s[1], list) and len(s[1]) == 3
                    and s[1][0] == "=" and isinstance(s[1][1], str) and _ALIAS.match(s[1][1])
                    and self.decls.get(s[1][1], (None,))[0] == "Int"):
                defs.setdefault(s[1][1], []).append((s[1][2], c.line))
        for name, (sort, dline) in self.decls.items():
            m = _ALIAS.match(name)
            if not m or sort != "Int":
                continue
            v = m.group(1)
            w = _bv_width(self.decls.get(v, (None,))[0])
            if w is None:
                self.add("ALIAS", dline, f"alias {name}: {v} is not a declared bit-vector")
                continue
            ds = defs.get(name, [])
            if not ds:
                self.add("ALIAS", dline, f"alias {name} has no definition (= {name} ...)")
                continue
            for rhs, line in ds[1:]:
                self.add("ALIAS", line, f"alias {name} defined more than once")
            rhs, line = ds[0]
            if rhs != _alias_def(v, w):
                self.add("ALIAS", line, f"alias {name} is not (- (bv2nat {v}) (* {2 ** w} (bv2nat ((_ extract {w - 1} {w - 1}) {v}))))")
            elif line not in range_lines:
                self.add("ALIAS", line, f"alias {name} is defined outside the range section")


def _poly_decl(c: Command) -> bool:
    if c.head in ("declare-datatype", "declare-datatypes", "declare-sort", "define-sort"):
        return True
    return c.head in DECL_HEADS and len(c.sexpr) > 1 and c.sexpr[1] in PRELUDE_NAMES


def _flat(sexpr) -> str:
    from .writer import to_str
    return to_str(sexpr)


def _mentions_poly(sexpr) -> bool:
    from .reader import atoms
    names = set(POLY_CONSTRUCTORS) | set(POLY_PREDICATES)
    return any(a in names for a in atoms(sexpr))


def lint_text(text: str, path: str = "", profile: str = "strict", z3_cfg=None) -> list[Diag]:
    """Lint one file. With z3_cfg (a Config), also run the PARSE rule through z3."""
    try:
        mix = parse(text, path)
    except ParseError as e:
        return [Diag("PARSE", E, e.line, f"s-expression syntax: {e}", path)]
    L = _Linter(mix, text)
    L.check_set_logic()
    L.check_poly_decl()
    L.collect_decls()
    L.check_terms()
    secs = L.check_sections()
    if secs is not None:
        L.check_goal(secs)
        L.check_layout(secs)
        L.check_decl_order(secs)
        L.check_alias(secs)
    if z3_cfg is not None:
        from ..oracle import z3_parse_errors
        for line, msg in z3_parse_errors(z3_cfg, text):
            L.add("PARSE", line, f"z3: {msg}")
    out = []
    for code, line, msg in L.found:
        r = RULES[code]
        out.append(Diag(code, r.strict if profile == "strict" else r.consumer, line, msg, path))
    out.sort(key=lambda d: (d.line or 0, d.code))
    return out


def lint_file(path: str | Path, profile: str = "strict", z3_cfg=None, display: str | None = None) -> list[Diag]:
    return lint_text(Path(path).read_text(encoding="utf-8"), display or str(path), profile, z3_cfg)


# ------------------------------------------------------------------ baseline
def summarize(diags: list[Diag]) -> dict[str, int]:
    """Warning counts per tag (the unit a baseline compares)."""
    out: dict[str, int] = {}
    for d in diags:
        if d.severity == W:
            out[d.tag] = out.get(d.tag, 0) + 1
    return dict(sorted(out.items()))


def load_baseline(path: str | Path) -> dict:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def dump_baseline(path: str | Path, profile: str, files: dict[str, dict[str, int]]) -> None:
    data = {"profile": profile, "files": dict(sorted(files.items()))}
    Path(path).write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
