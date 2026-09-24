"""Component P: a parser for the LLVM 18 textual IR subset c2mix accepts (spec §5.4, appendix B).

Reading LLVM's own text rather than binding to a library is D2: llvmlite ships its own
LLVM, which need not agree with the clang that produced the file. The price is that the
parser has to be trusted, which is what A3.2 buys back — parse, print, and let
`llvm-as-18` and `llvm-diff-18` say whether the module survived the trip.

Anything outside the subset is refused with the source line attached (`E-UNSUPPORTED`),
never silently dropped. Module-level text the executor has no opinion about (attribute
groups, metadata definitions, `declare` lines) is kept verbatim as `Raw` items; the
debug metadata table is additionally indexed, for line numbers (§5.1) and for the
signedness of named locals (`DIBasicType`).
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field

TERMINATORS = {"br", "switch", "ret", "unreachable"}

# Flags that make an instruction able to produce poison; the executor refuses them
# (E-POISON-FLAG) so it never has to model poison. `inbounds` is ignored (appendix B).
POISON_FLAGS = {"nsw", "nuw", "exact", "nneg", "disjoint", "samesign"}
IGNORED_FLAGS = {"inbounds", "inrange"}

BINOPS = {"add", "sub", "mul", "and", "or", "xor", "shl", "lshr", "ashr"}
CASTS = {"trunc", "zext", "sext"}
REJECTED_OPS = {
    "fadd": "E-FLOAT", "fsub": "E-FLOAT", "fmul": "E-FLOAT", "fdiv": "E-FLOAT",
    "frem": "E-FLOAT", "fcmp": "E-FLOAT", "fptosi": "E-FLOAT", "fptoui": "E-FLOAT",
    "sitofp": "E-FLOAT", "uitofp": "E-FLOAT", "fneg": "E-FLOAT",
    "udiv": "E-DIV", "sdiv": "E-DIV", "urem": "E-DIV", "srem": "E-DIV",
    "extractvalue": "E-UNSUPPORTED", "insertvalue": "E-UNSUPPORTED",
    "extractelement": "E-VECTOR", "insertelement": "E-VECTOR", "shufflevector": "E-VECTOR",
    "invoke": "E-UNSUPPORTED", "landingpad": "E-UNSUPPORTED", "resume": "E-UNSUPPORTED",
    "atomicrmw": "E-UNSUPPORTED", "cmpxchg": "E-UNSUPPORTED", "fence": "E-UNSUPPORTED",
    "va_arg": "E-UNSUPPORTED", "indirectbr": "E-UNSUPPORTED", "callbr": "E-UNSUPPORTED",
    "inttoptr": "E-UNSUPPORTED", "ptrtoint": "E-UNSUPPORTED", "bitcast": "E-UNSUPPORTED",
    "addrspacecast": "E-UNSUPPORTED", "freeze": "E-UNSUPPORTED",
}


class ParseError(Exception):
    """Something outside the supported subset. `code` is the spec's error code."""

    def __init__(self, message: str, code: str = "E-UNSUPPORTED", line: int | None = None):
        super().__init__(message if line is None else f"{message} (at {line})")
        self.code, self.line, self.message = code, line, message
        self.text = ""                  # the instruction, for resolving its source line
        self.source = None              # the C source line, once the metadata is known


# --------------------------------------------------------------------------- types
@dataclass(frozen=True)
class Type:
    kind: str                       # void | int | ptr | array | struct | label | opaque
    bits: int = 0
    elem: "Type | None" = None
    count: int = 0
    fields: tuple = ()
    packed: bool = False
    raw: str = ""                   # opaque: the original text

    def __str__(self) -> str:
        if self.raw and self.kind == "struct":
            return self.raw                      # a named type keeps its name
        if self.kind == "int":
            return f"i{self.bits}"
        if self.kind == "array":
            return f"[{self.count} x {self.elem}]"
        if self.kind == "struct":
            inner = ", ".join(str(f) for f in self.fields)
            return ("<{ " + inner + " }>") if self.packed else ("{ " + inner + " }")
        return {"void": "void", "ptr": "ptr", "label": "label"}.get(self.kind, self.raw)

    @property
    def size(self) -> int:
        """Size in bytes, with the natural layout clang uses for this subset."""
        if self.kind == "int":
            return max(1, (self.bits + 7) // 8)
        if self.kind == "ptr":
            return 8
        if self.kind == "array":
            return self.count * self.elem.size
        if self.kind == "struct":
            total, align = 0, 1
            for f in self.fields:
                a = 1 if self.packed else f.align
                align = max(align, a)
                total = (total + a - 1) // a * a + f.size
            return (total + align - 1) // align * align
        raise ParseError(f"no size for type {self}")

    @property
    def align(self) -> int:
        if self.kind in ("int", "ptr"):
            return self.size
        if self.kind == "array":
            return self.elem.align
        if self.kind == "struct":
            return 1 if self.packed else max((f.align for f in self.fields), default=1)
        return 1


VOID = Type("void")
PTR = Type("ptr")
LABEL = Type("label")

# `%struct.pair = type { i32, i32 }` — a module's named types, filled in by parse().
# They are kept by name so the printer writes `%struct.pair` back, not its expansion.
NAMED_TYPES: dict = {}


def int_type(bits: int) -> Type:
    return Type("int", bits)


# ------------------------------------------------------------------------ operands
@dataclass(frozen=True)
class Reg:
    name: str                       # with the leading %

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class GlobalRef:
    name: str                       # with the leading @

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class IntLit:
    value: int
    boolean: bool = False           # written as true/false, as LLVM prints i1

    def __str__(self) -> str:
        if self.boolean:
            return "true" if self.value else "false"
        return str(self.value)


@dataclass(frozen=True)
class Special:
    word: str                       # undef | poison | null | zeroinitializer | none

    def __str__(self) -> str:
        return self.word


@dataclass(frozen=True)
class Aggregate:
    kind: str                       # array | struct
    elems: tuple                    # (Type, operand) pairs
    packed: bool = False

    def __str__(self) -> str:
        inner = ", ".join(f"{t} {v}" for t, v in self.elems)
        if self.kind == "array":
            return f"[{inner}]"
        return ("<{ " + inner + " }>") if self.packed else ("{ " + inner + " }")


@dataclass(frozen=True)
class StringLit:
    text: str                       # the raw c"..." body

    def __str__(self) -> str:
        return f'c"{self.text}"'


@dataclass(frozen=True)
class ConstExpr:
    raw: str

    def __str__(self) -> str:
        return self.raw


@dataclass(frozen=True)
class MetaRef:
    raw: str

    def __str__(self) -> str:
        return self.raw


# --------------------------------------------------------------------- instructions
@dataclass
class Arg:
    """One call argument: a type, attributes, and a value — or raw text for metadata."""
    ty: Type | None
    attrs: tuple
    value: object
    raw: str = ""

    def __str__(self) -> str:
        if self.ty is None:
            return self.raw
        parts = [str(self.ty), *self.attrs, str(self.value)]
        return " ".join(parts)


@dataclass
class Instr:
    op: str
    result: str | None = None
    ty: Type | None = None          # operand type (binops, icmp, load result, …)
    ty2: Type | None = None         # cast target
    args: tuple = ()
    flags: tuple = ()
    pred: str | None = None
    labels: tuple = ()              # br/switch destinations
    cases: tuple = ()               # switch: (Type, IntLit, label)
    incoming: tuple = ()            # phi: (value, label)
    callee: str | None = None
    call_args: tuple = ()
    head: tuple = ()                # tokens before the type (tail, cconv, ret attrs)
    trail: str = ""                 # tokens after the operands (fn attrs, align, …)
    meta: str = ""                  # ", !dbg !51, !tbaa !3"
    line: int | None = None         # source line, from !dbg
    ir_line: int = 0                # line number inside the .ll file
    text: str = ""                  # original text, for diagnostics

    def where(self, func: str = "") -> str:
        at = f"{func}:" if func else ""
        return f"{at}{self.ir_line}" + (f" (source line {self.line})" if self.line else "")


@dataclass
class Block:
    label: str                      # without the trailing colon; "" for an implicit entry
    instrs: list = field(default_factory=list)
    explicit: bool = True


@dataclass
class Param:
    ty: Type
    attrs: tuple
    name: str | None

    def __str__(self) -> str:
        return " ".join([str(self.ty), *self.attrs, *( [self.name] if self.name else [])])


@dataclass
class Function:
    name: str                       # with the leading @
    ret_ty: Type
    head: tuple                     # tokens between "define" and the return type
    ret_attrs: tuple
    params: list
    varargs: bool
    trail: str                      # tokens after ")" up to "{"
    blocks: list = field(default_factory=list)
    ir_line: int = 0

    def block(self, label: str) -> Block:
        for b in self.blocks:
            if b.label == label:
                return b
        raise ParseError(f"{self.name}: no block {label}")


@dataclass
class Global:
    name: str
    head: tuple                     # linkage / visibility tokens
    constant: bool
    ty: Type
    init: object | None
    trail: str
    ir_line: int = 0


@dataclass
class Raw:
    text: str


@dataclass
class Module:
    items: list = field(default_factory=list)
    metadata: dict = field(default_factory=dict)     # "!42" -> raw text

    @property
    def functions(self) -> list:
        return [i for i in self.items if isinstance(i, Function)]

    @property
    def globals(self) -> list:
        return [i for i in self.items if isinstance(i, Global)]

    def function(self, name: str):
        for f in self.functions:
            if f.name == name.lstrip("@") or f.name == "@" + name.lstrip("@"):
                return f
        return None

    def global_(self, name: str):
        for g in self.globals:
            if g.name == name or g.name == "@" + name.lstrip("@"):
                return g
        return None


# ----------------------------------------------------------------------- the lexer
TOKEN = re.compile(r"""
      (?P<space>[ \t]+)
    | (?P<comment>;[^\n]*)
    | (?P<string>c?"(?:[^"\\]|\\.)*")
    | (?P<id>[%@!][%@!]?(?:"(?:[^"\\]|\\.)*"|[-a-zA-Z$._0-9]+))
    | (?P<attrgrp>\#[0-9]+)
    | (?P<hex>0x[0-9A-Fa-f]+)
    | (?P<num>-?[0-9]+)
    | (?P<word>[-a-zA-Z$._][-a-zA-Z$._0-9]*)
    | (?P<punct>[{}\[\]()<>,*=:])
""", re.X)


class Lexer:
    def __init__(self, text: str, line: int = 0):
        self.text, self.line = text, line
        self.toks: list[str] = []
        pos = 0
        while pos < len(text):
            m = TOKEN.match(text, pos)
            if not m:
                raise ParseError(f"cannot tokenize {text[pos:pos + 20]!r}", line=line)
            pos = m.end()
            if m.lastgroup in ("space", "comment"):
                continue
            self.toks.append(m.group())
        self.i = 0

    def peek(self, k: int = 0) -> str | None:
        j = self.i + k
        return self.toks[j] if j < len(self.toks) else None

    def next(self) -> str:
        if self.i >= len(self.toks):
            raise ParseError("unexpected end of instruction", line=self.line)
        self.i += 1
        return self.toks[self.i - 1]

    def eat(self, tok: str) -> bool:
        if self.peek() == tok:
            self.i += 1
            return True
        return False

    def expect(self, tok: str) -> str:
        if self.peek() != tok:
            raise ParseError(f"expected {tok!r}, found {self.peek()!r}", line=self.line)
        return self.next()

    def rest(self) -> str:
        out = _join(self.toks[self.i:])
        self.i = len(self.toks)
        return out

    @property
    def done(self) -> bool:
        return self.i >= len(self.toks)


INT_TY = re.compile(r"i([0-9]+)$")
VEC_START = "<"


def parse_type(lx: Lexer) -> Type:
    t = lx.peek()
    if t is None:
        raise ParseError("expected a type", line=lx.line)
    if t == VEC_START and lx.peek(1) != "{":
        raise ParseError("vector types are not supported", "E-VECTOR", lx.line)
    if t == "[":
        lx.next()
        count = int(lx.next())
        if lx.next() != "x":
            raise ParseError("expected 'x' in an array type", line=lx.line)
        elem = parse_type(lx)
        lx.expect("]")
        return Type("array", elem=elem, count=count)
    if t in ("{", "<"):
        packed = lx.next() == "<"
        if packed:
            lx.expect("{")
        fields = []
        if not lx.eat("}"):
            fields.append(parse_type(lx))
            while lx.eat(","):
                fields.append(parse_type(lx))
            lx.expect("}")
        if packed:
            lx.expect(">")
        return Type("struct", fields=tuple(fields), packed=packed)
    m = INT_TY.match(t)
    if m:
        lx.next()
        bits = int(m.group(1))
        if not 1 <= bits <= 128:
            raise ParseError(f"integer width {bits} outside [1, 128]", line=lx.line)
        return int_type(bits)
    if t == "ptr":
        lx.next()
        return PTR
    if t == "void":
        lx.next()
        return VOID
    if t == "label":
        lx.next()
        return LABEL
    if t in ("half", "float", "double", "fp128", "x86_fp80", "bfloat"):
        raise ParseError(f"floating point type {t}", "E-FLOAT", lx.line)
    if t.startswith("%") and t in NAMED_TYPES:
        lx.next()
        return NAMED_TYPES[t]
    raise ParseError(f"unsupported type {t!r}", line=lx.line)


def looks_like_type(tok: str | None) -> bool:
    return tok is not None and (tok in ("ptr", "void", "label", "[", "{", "<")
                                or bool(INT_TY.match(tok)) or tok in NAMED_TYPES)


CONST_EXPR_HEADS = {"getelementptr", "bitcast", "ptrtoint", "inttoptr", "trunc", "zext",
                    "sext", "add", "sub", "mul", "and", "or", "xor", "shl", "lshr", "ashr",
                    "select", "icmp", "addrspacecast"}


def parse_value(lx: Lexer) -> object:
    t = lx.peek()
    if t is None:
        raise ParseError("expected a value", line=lx.line)
    if t.startswith("%") or t.startswith("@"):
        return Reg(lx.next()) if t.startswith("%") else GlobalRef(lx.next())
    if t.startswith("!"):
        return MetaRef(lx.next())
    if t in ("undef", "poison", "null", "zeroinitializer", "none"):
        return Special(lx.next())
    if t in ("true", "false"):
        return IntLit(1 if lx.next() == "true" else 0, boolean=True)
    if t.startswith('c"'):
        return StringLit(lx.next()[2:-1])
    if t.startswith("0x"):
        return IntLit(int(lx.next(), 16))
    if re.fullmatch(r"-?[0-9]+", t):
        return IntLit(int(lx.next()))
    if t == "[":
        lx.next()
        elems = []
        if not lx.eat("]"):
            while True:
                ty = parse_type(lx)
                elems.append((ty, parse_value(lx)))
                if not lx.eat(","):
                    break
            lx.expect("]")
        return Aggregate("array", tuple(elems))
    if t in ("{", "<"):
        packed = lx.next() == "<"
        if packed:
            lx.expect("{")
        elems = []
        if not lx.eat("}"):
            while True:
                ty = parse_type(lx)
                elems.append((ty, parse_value(lx)))
                if not lx.eat(","):
                    break
            lx.expect("}")
        if packed:
            lx.expect(">")
        return Aggregate("struct", tuple(elems), packed)
    if t in CONST_EXPR_HEADS:
        return ConstExpr(_balanced(lx))
    raise ParseError(f"unsupported value {t!r}", line=lx.line)


def _balanced(lx: Lexer) -> str:
    """A constant expression: a head word followed by a parenthesised body."""
    out = [lx.next()]
    while lx.peek() in ("inbounds", "nsw", "nuw", "exact"):
        out.append(lx.next())
    depth = 0
    while True:
        tok = lx.next()
        out.append(tok)
        depth += tok == "("
        depth -= tok == ")"
        if depth == 0:
            break
    return _join(out)


def _join(toks: list[str]) -> str:
    out = ""
    for t in toks:
        if out and not (t in (",", ")", "]", "}") or out.endswith(("(", "[", "{"))
                        or (t == "(" and out.rsplit(" ", 1)[-1].startswith("!"))):
            out += " "
        out += t
    return out


# ---------------------------------------------------------------- instruction level
def _split_meta(lx: Lexer) -> str:
    """Trailing metadata attachments, kept verbatim: they carry no semantics for us,
    but they must come back out unchanged for A3.2."""
    out = []
    while lx.peek() == "," and (lx.peek(1) or "").startswith("!"):
        lx.next()
        key = lx.next()
        val = lx.next()
        out.append(f", {key} {val}")
    return "".join(out)


def _trail(lx: Lexer) -> str:
    """Everything after the operands that is not a metadata attachment — `align 2`
    and friends. Stopping at the first `, !…` is what keeps `!dbg` in `meta`, where
    the line numbers come from."""
    out = []
    while not lx.done:
        if lx.peek() == "," and (lx.peek(1) or "").startswith("!"):
            break
        if (lx.peek() or "").startswith("!"):
            break
        out.append(lx.next())
    return _join(out)


def _flags(lx: Lexer) -> tuple:
    out = []
    while lx.peek() in POISON_FLAGS | IGNORED_FLAGS:
        out.append(lx.next())
    return tuple(out)


def parse_instr(text: str, ir_line: int) -> Instr:
    try:
        return _parse_instr(text, ir_line)
    except ParseError as e:
        e.text = e.text or text
        raise


def _parse_instr(text: str, ir_line: int) -> Instr:
    lx = Lexer(text, ir_line)
    result = None
    if (lx.peek() or "").startswith("%") and lx.peek(1) == "=":
        result = lx.next()
        lx.next()
    head = []
    while lx.peek() in ("tail", "musttail", "notail"):
        head.append(lx.next())
    op = lx.next()
    if op in REJECTED_OPS:
        raise ParseError(f"{op} is outside the supported subset", REJECTED_OPS[op], ir_line)
    ins = Instr(op=op, result=result, head=tuple(head), ir_line=ir_line, text=text)

    if op in BINOPS:
        ins.flags = _flags(lx)
        ins.ty = parse_type(lx)
        a = parse_value(lx)
        lx.expect(",")
        ins.args = (a, parse_value(lx))
    elif op in CASTS:
        ins.flags = _flags(lx)
        ins.ty = parse_type(lx)
        ins.args = (parse_value(lx),)
        if lx.next() != "to":
            raise ParseError(f"{op}: expected 'to'", line=ir_line)
        ins.ty2 = parse_type(lx)
    elif op == "icmp":
        ins.flags = _flags(lx)
        ins.pred = lx.next()
        ins.ty = parse_type(lx)
        a = parse_value(lx)
        lx.expect(",")
        ins.args = (a, parse_value(lx))
    elif op == "select":
        ins.flags = _flags(lx)
        cond_ty = parse_type(lx)
        cond = parse_value(lx)
        lx.expect(",")
        ins.ty = parse_type(lx)
        a = parse_value(lx)
        lx.expect(",")
        parse_type(lx)
        b = parse_value(lx)
        ins.args = (cond, a, b)
        ins.ty2 = cond_ty
    elif op == "alloca":
        ins.flags = _flags(lx)
        ins.ty = parse_type(lx)
        if lx.eat(","):
            if looks_like_type(lx.peek()):
                ins.ty2 = parse_type(lx)
                ins.args = (parse_value(lx),)
                if lx.eat(","):
                    ins.trail = _trail(lx)
            else:
                ins.trail = _trail(lx)
    elif op == "load":
        ins.ty = parse_type(lx)
        lx.expect(",")
        parse_type(lx)                      # always ptr with opaque pointers
        ins.args = (parse_value(lx),)
        ins.meta = _split_meta(lx)
        if lx.eat(","):
            ins.trail = _trail(lx)
        ins.meta += _split_meta(lx)
    elif op == "store":
        ins.ty = parse_type(lx)
        v = parse_value(lx)
        lx.expect(",")
        parse_type(lx)
        ins.args = (v, parse_value(lx))
        ins.meta = _split_meta(lx)
        if lx.eat(","):
            ins.trail = _trail(lx)
        ins.meta += _split_meta(lx)
    elif op == "getelementptr":
        ins.flags = _flags(lx)
        ins.ty = parse_type(lx)
        lx.expect(",")
        parse_type(lx)
        base = parse_value(lx)
        idx = []
        idx_ty = []
        while lx.eat(","):
            if not looks_like_type(lx.peek()):
                lx.i -= 1
                break
            idx_ty.append(parse_type(lx))
            idx.append(parse_value(lx))
        ins.args = (base, *idx)
        ins.cases = tuple(idx_ty)
    elif op == "phi":
        ins.flags = _flags(lx)
        ins.ty = parse_type(lx)
        pairs = []
        while True:
            lx.expect("[")
            v = parse_value(lx)
            lx.expect(",")
            lbl = lx.next()
            lx.expect("]")
            pairs.append((v, lbl))
            if not (lx.peek() == "," and lx.peek(1) == "["):
                break
            lx.next()
        ins.incoming = tuple(pairs)
    elif op == "br":
        if lx.peek() == "label":
            lx.next()
            ins.labels = (lx.next(),)
        else:
            ins.ty = parse_type(lx)
            ins.args = (parse_value(lx),)
            lx.expect(",")
            lx.expect("label")
            t = lx.next()
            lx.expect(",")
            lx.expect("label")
            ins.labels = (t, lx.next())
    elif op == "switch":
        ins.ty = parse_type(lx)
        ins.args = (parse_value(lx),)
        lx.expect(",")
        lx.expect("label")
        ins.labels = (lx.next(),)
        lx.expect("[")
        cases = []
        while not lx.eat("]"):
            ty = parse_type(lx)
            val = parse_value(lx)
            lx.expect(",")
            lx.expect("label")
            cases.append((ty, val, lx.next()))
        ins.cases = tuple(cases)
    elif op == "ret":
        ins.ty = parse_type(lx)
        if ins.ty.kind != "void":
            ins.args = (parse_value(lx),)
    elif op == "unreachable":
        pass
    elif op == "call":
        while lx.peek() in ("fast", "nsz", "arcp", "contract", "afn", "reassoc", "ninf",
                            "nnan") or (lx.peek() or "").startswith("ccc"):
            head.append(lx.next())
        ret_attrs = []
        while not looks_like_type(lx.peek()):
            tok = lx.next()
            if tok == "(":                  # a parameterised attribute such as align(8)
                depth = 1
                while depth:
                    depth += lx.peek() == "("
                    depth -= lx.peek() == ")"
                    ret_attrs.append(lx.next())
                continue
            ret_attrs.append(tok)
        ins.head = tuple(head)
        ins.flags = tuple(ret_attrs)
        ins.ty = parse_type(lx)
        callee = lx.next()
        if not callee.startswith("@"):
            raise ParseError(f"indirect call through {callee}", "E-EXTERNAL-CALL", ir_line)
        ins.callee = callee
        ins.call_args = _call_args(lx)
        ins.meta = _split_meta(lx)
        if not lx.done:
            ins.trail = _trail(lx)
    else:
        raise ParseError(f"unsupported instruction {op!r}", line=ir_line)

    ins.meta += _split_meta(lx)
    if not lx.done and not ins.trail and op not in ("call", "load", "store", "alloca"):
        ins.trail = lx.rest()
    return ins


def _call_args(lx: Lexer) -> tuple:
    lx.expect("(")
    args = []
    if lx.eat(")"):
        return ()
    while True:
        if lx.peek() == "metadata":
            toks = [lx.next()]
            depth = 0
            while True:
                nxt = lx.peek()
                if nxt is None or (depth == 0 and nxt in (",", ")")):
                    break
                depth += nxt == "("
                depth -= nxt == ")"
                toks.append(lx.next())
            args.append(Arg(None, (), None, _join(toks)))
        else:
            ty = parse_type(lx)
            attrs = []
            while not (lx.peek() or "").startswith(("%", "@", "!")) and \
                    lx.peek() not in (",", ")") and not _is_literal(lx.peek()):
                tok = lx.next()
                if tok in SIZED_ATTRS and re.fullmatch(r"[0-9]+", lx.peek() or ""):
                    attrs += [tok, lx.next()]    # `align 16`, `dereferenceable 32`
                    continue
                if tok == "(":
                    depth = 1
                    while depth:
                        depth += lx.peek() == "("
                        depth -= lx.peek() == ")"
                        attrs.append(lx.next())
                    continue
                attrs.append(tok)
            args.append(Arg(ty, tuple(attrs), parse_value(lx)))
        if not lx.eat(","):
            break
    lx.expect(")")
    return tuple(args)


def _is_literal(tok: str | None) -> bool:
    return tok is not None and (re.fullmatch(r"-?[0-9]+", tok) is not None
                                or tok.startswith("0x") or tok.startswith('c"')
                                or tok in ("true", "false", "undef", "poison", "null",
                                           "zeroinitializer", "[", "{")
                                or tok in CONST_EXPR_HEADS)


# --------------------------------------------------------------------- module level
DEF_RE = re.compile(r"^define\b")
GLOBAL_RE = re.compile(r"^(@[-a-zA-Z$._0-9]+|@\"[^\"]*\")\s*=")
META_DEF_RE = re.compile(r"^(![-a-zA-Z$._0-9]+)\s*=")


TYPE_DEF_RE = re.compile(r"^(%[-a-zA-Z$._0-9]+)\s*=\s*type\s+(.*)$")


def parse(text: str, path: str = "<ir>") -> Module:
    mod = Module()
    lines = text.splitlines()
    locs = _locations(text)
    _collect_named_types(lines)
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if DEF_RE.match(stripped):
            try:
                fn, i = _parse_function(lines, i)
            except ParseError as e:
                raise _with_source(e, locs)
            mod.items.append(fn)
            continue
        if GLOBAL_RE.match(stripped):
            mod.items.append(_parse_global(stripped, i + 1))
            i += 1
            continue
        m = META_DEF_RE.match(stripped)
        if m:
            mod.metadata[m.group(1)] = stripped
        mod.items.append(Raw(line))
        i += 1
    return mod


def _collect_named_types(lines: list[str]) -> None:
    """`%struct.pair = type { i32, i32 }`. Collected first, because a definition may
    appear after the function that uses it."""
    NAMED_TYPES.clear()
    pending = []
    for n, line in enumerate(lines):
        m = TYPE_DEF_RE.match(line.strip())
        if m:
            pending.append((m.group(1), m.group(2).strip(), n + 1))
    for _ in range(len(pending) + 1):            # resolve references between them
        left = []
        for name, body, ln in pending:
            try:
                ty = parse_type(Lexer(body, ln))
            except ParseError:
                left.append((name, body, ln))
                continue
            NAMED_TYPES[name] = Type(ty.kind, ty.bits, ty.elem, ty.count, ty.fields,
                                     ty.packed, raw=name)
        if not left:
            break
        pending = left


def _locations(text: str) -> dict:
    """`!N -> source line`, scanned before parsing so a rejected instruction can still
    say which line of C it came from (A3.7)."""
    out = {}
    for line in text.splitlines():
        m = re.match(r"(![-a-zA-Z$._0-9]+)\s*=\s*!DILocation\(line:\s*(\d+)", line.strip())
        if m:
            out[m.group(1)] = int(m.group(2))
    return out


def _with_source(e: ParseError, locs: dict) -> ParseError:
    m = DBG_ATTACH_RE.search(e.text or "")
    if m:
        e.source = locs.get(m.group(1))
        if e.source is not None:
            e.args = (f"{e.message} (source line {e.source})",)
    return e


def _parse_global(text: str, ir_line: int) -> Global:
    lx = Lexer(text, ir_line)
    name = lx.next()
    lx.expect("=")
    head = []
    while lx.peek() not in ("constant", "global", "external", "alias"):
        head.append(lx.next())
    kw = lx.next()
    if kw == "external":
        head.append(kw)
        kw = lx.next()
    constant = kw == "constant"
    head.append(kw)
    ty = parse_type(lx)
    init = None
    if not lx.done and lx.peek() != ",":
        init = parse_value(lx)
    trail = ""
    if lx.eat(","):
        trail = lx.rest()
    head = tuple(h for h in head if h not in ("constant", "global"))
    return Global(name, head, constant, ty, init, trail, ir_line)


def _parse_function(lines: list[str], i: int) -> tuple[Function, int]:
    header, start = lines[i].rstrip(), i
    while not header.rstrip().endswith("{"):
        i += 1
        header += " " + lines[i].strip()
    fn = _parse_header(header.rstrip()[:-1].strip(), start + 1)
    i += 1
    # An unnamed entry block still has a number, and phi nodes name it: LLVM counts
    # the unnamed arguments first, so the entry block is the next number after them.
    unnamed = sum(1 for p in fn.params if p.name and re.fullmatch(r"%[0-9]+", p.name))
    cur = Block(str(unnamed), explicit=False)
    fn.blocks.append(cur)
    while lines[i].strip() != "}":
        raw = lines[i]
        s = raw.split(";")[0].strip() if not raw.strip().startswith(";") else ""
        while s and _unbalanced(s):              # a switch spreads its cases over lines
            i += 1
            nxt = lines[i]
            s += " " + (nxt.split(";")[0].strip() if not nxt.strip().startswith(";") else "")
        if s:
            m = re.fullmatch(r'([-a-zA-Z$._0-9]+|"[^"]*"):', s)
            if m:
                cur = Block(m.group(1))
                fn.blocks.append(cur)
            else:
                cur.instrs.append(parse_instr(s, i + 1))
        i += 1
    if not fn.blocks[0].instrs and len(fn.blocks) > 1:
        fn.blocks.pop(0)
    return fn, i + 1


def _unbalanced(text: str) -> bool:
    depth = 0
    for ch in text:
        depth += ch in "([{"
        depth -= ch in ")]}"
    return depth > 0


def _parse_header(text: str, ir_line: int) -> Function:
    lx = Lexer(text, ir_line)
    lx.expect("define")
    # The function name is the first @ token at paren depth 0.
    depth, name_at = 0, None
    for j in range(lx.i, len(lx.toks)):
        t = lx.toks[j]
        depth += t == "("
        depth -= t == ")"
        if depth == 0 and t.startswith("@"):
            name_at = j
            break
    if name_at is None:
        raise ParseError("no function name in the define line", line=ir_line)
    prefix = lx.toks[lx.i:name_at]
    head, ret_ty, ret_attrs = _split_return_type(prefix, ir_line)
    name = lx.toks[name_at]
    lx.i = name_at + 1
    params, varargs = _parse_params(lx)
    trail = lx.rest()
    return Function(name, ret_ty, head, ret_attrs, params, varargs, trail, ir_line=ir_line)


RET_ATTRS = {"signext", "zeroext", "noundef", "nonnull", "inreg", "noalias", "nofpclass"}
SIZED_ATTRS = {"align", "dereferenceable", "dereferenceable_or_null"}


def _split_return_type(prefix: list[str], ir_line: int) -> tuple[tuple, Type, tuple]:
    """`prefix` holds everything between `define` and the function name; its tail is the
    return type, everything before it is linkage/visibility/return attributes."""
    for start in range(len(prefix)):
        try:
            lx = Lexer(" ".join(prefix[start:]), ir_line)
            ty = parse_type(lx)
        except ParseError:
            continue
        if lx.done:
            head = [t for t in prefix[:start] if t not in RET_ATTRS]
            attrs = [t for t in prefix[:start] if t in RET_ATTRS]
            return tuple(head), ty, tuple(attrs)
    raise ParseError(f"cannot find the return type in {' '.join(prefix)!r}", line=ir_line)


def _parse_params(lx: Lexer) -> tuple[list, bool]:
    lx.expect("(")
    params, varargs = [], False
    if lx.eat(")"):
        return params, varargs
    while True:
        if lx.peek() == "...":
            lx.next()
            varargs = True
            break
        ty = parse_type(lx)
        attrs, name = [], None
        while lx.peek() not in (",", ")"):
            tok = lx.next()
            if tok == "(":
                depth = 1
                while depth:
                    depth += lx.peek() == "("
                    depth -= lx.peek() == ")"
                    attrs.append(lx.next())
                continue
            if tok.startswith("%"):
                name = tok
            else:
                attrs.append(tok)
        params.append(Param(ty, tuple(attrs), name))
        if not lx.eat(","):
            break
    lx.expect(")")
    return params, varargs


# ------------------------------------------------------------------- debug metadata
LOC_RE = re.compile(r"!DILocation\(line:\s*(\d+)")
VAR_TYPE_RE = re.compile(r"!DILocalVariable\(.*?\btype:\s*(![-a-zA-Z$._0-9]+)")
VAR_NAME_RE = re.compile(r'!DILocalVariable\(name:\s*"([^"]*)"')
BASIC_RE = re.compile(r"!DIBasicType\(.*?\bencoding:\s*(DW_ATE_[a-z_]+)")
BASETYPE_RE = re.compile(r"!DI(?:Derived|Composite)Type\(.*?\bbaseType:\s*(![-a-zA-Z$._0-9]+)")
DBG_ATTACH_RE = re.compile(r"!dbg\s+(![-a-zA-Z$._0-9]+)")

SIGNED_ENCODINGS = {"DW_ATE_signed", "DW_ATE_signed_char"}
UNSIGNED_ENCODINGS = {"DW_ATE_unsigned", "DW_ATE_unsigned_char", "DW_ATE_boolean"}


class DebugInfo:
    """The debug metadata the frontend actually uses: `!dbg` line numbers (§5.1) and
    the signedness of named C locals (`DIBasicType`, rule 3 of §5.1)."""

    def __init__(self, mod: Module):
        self.md = mod.metadata

    def line(self, ref: str | None) -> int | None:
        node = self.md.get(ref or "")
        if not node:
            return None
        m = LOC_RE.search(node)
        return int(m.group(1)) if m else None

    def var_signed(self, ref: str | None) -> bool | None:
        node = self.md.get(ref or "")
        if not node:
            return None
        m = VAR_TYPE_RE.search(node)
        return self.type_signed(m.group(1)) if m else None

    def var_name(self, ref: str | None) -> str | None:
        node = self.md.get(ref or "")
        m = VAR_NAME_RE.search(node) if node else None
        return m.group(1) if m else None

    def type_signed(self, ref: str | None, depth: int = 0) -> bool | None:
        node = self.md.get(ref or "")
        if not node or depth > 8:
            return None
        m = BASIC_RE.search(node)
        if m:
            if m.group(1) in SIGNED_ENCODINGS:
                return True
            if m.group(1) in UNSIGNED_ENCODINGS:
                return False
            return None
        m = BASETYPE_RE.search(node)
        return self.type_signed(m.group(1), depth + 1) if m else None


def attach_lines(mod: Module) -> None:
    """Fill in Instr.line from the `!dbg` attachments (§5.1: every value carries a
    source position). Called once after parsing, before the executor runs."""
    dbg = DebugInfo(mod)
    for fn in mod.functions:
        for blk in fn.blocks:
            for ins in blk.instrs:
                m = DBG_ATTACH_RE.search(ins.meta or "")
                if m:
                    ins.line = dbg.line(m.group(1))


# ---------------------------------------------------------------------- the printer
def render(mod: Module) -> str:
    """Print a parsed module back as LLVM text. A3.2 feeds the result to `llvm-as-18`
    and `llvm-diff-18`: every instruction here comes out of the parsed structure, so a
    field the parser dropped shows up as a difference."""
    out = []
    for item in mod.items:
        if isinstance(item, Raw):
            out.append(item.text)
        elif isinstance(item, Global):
            out.append(render_global(item))
        else:
            out.append(render_function(item))
    return "\n".join(out) + "\n"


def render_global(g: Global) -> str:
    parts = [g.name, "=", *g.head, "constant" if g.constant else "global", str(g.ty)]
    if g.init is not None:
        parts.append(str(g.init))
    text = " ".join(parts)
    return text + (f", {g.trail}" if g.trail else "")


def render_function(fn: Function) -> str:
    params = ", ".join(str(p) for p in fn.params) + (", ..." if fn.varargs else "")
    head = " ".join(["define", *fn.head, *fn.ret_attrs, str(fn.ret_ty)])
    out = [f"{head} {fn.name}({params})" + (f" {fn.trail}" if fn.trail else "") + " {"]
    for blk in fn.blocks:
        if blk.explicit:
            out.append(f"{blk.label}:")
        out += ["  " + render_instr(i) for i in blk.instrs]
    out.append("}")
    return "\n".join(out)


def render_instr(ins: Instr) -> str:
    op, a = ins.op, ins.args
    body: str
    if op in BINOPS:
        body = f"{op} {_fl(ins)}{ins.ty} {a[0]}, {a[1]}"
    elif op in CASTS:
        body = f"{op} {_fl(ins)}{ins.ty} {a[0]} to {ins.ty2}"
    elif op == "icmp":
        body = f"icmp {_fl(ins)}{ins.pred} {ins.ty} {a[0]}, {a[1]}"
    elif op == "select":
        body = f"select {_fl(ins)}{ins.ty2} {a[0]}, {ins.ty} {a[1]}, {ins.ty} {a[2]}"
    elif op == "alloca":
        body = f"alloca {_fl(ins)}{ins.ty}"
        if ins.ty2 is not None:
            body += f", {ins.ty2} {a[0]}"
        if ins.trail:
            body += f", {ins.trail}"
    elif op == "load":
        body = f"load {ins.ty}, ptr {a[0]}" + (f", {ins.trail}" if ins.trail else "")
    elif op == "store":
        body = f"store {ins.ty} {a[0]}, ptr {a[1]}" + (f", {ins.trail}" if ins.trail else "")
    elif op == "getelementptr":
        idx = "".join(f", {t} {v}" for t, v in zip(ins.cases, a[1:]))
        body = f"getelementptr {_fl(ins)}{ins.ty}, ptr {a[0]}{idx}"
    elif op == "phi":
        pairs = ", ".join(f"[ {v}, {l} ]" for v, l in ins.incoming)
        body = f"phi {_fl(ins)}{ins.ty} {pairs}"
    elif op == "br":
        body = (f"br label {ins.labels[0]}" if not a else
                f"br {ins.ty} {a[0]}, label {ins.labels[0]}, label {ins.labels[1]}")
    elif op == "switch":
        cases = " ".join(f"{t} {v}, label {l}" for t, v, l in ins.cases)
        body = f"switch {ins.ty} {a[0]}, label {ins.labels[0]} [{' ' + cases if cases else ''} ]"
    elif op == "ret":
        body = "ret void" if ins.ty.kind == "void" else f"ret {ins.ty} {a[0]}"
    elif op == "unreachable":
        body = "unreachable"
    elif op == "call":
        args = ", ".join(str(x) for x in ins.call_args)
        parts = [*ins.head, "call", *ins.flags, str(ins.ty)]
        body = " ".join(parts) + f" {ins.callee}({args})"
        if ins.trail:
            body += f" {ins.trail}"
    else:
        raise ParseError(f"cannot print {op!r}", line=ins.ir_line)
    if ins.result:
        body = f"{ins.result} = {body}"
    return body + ins.meta


def _fl(ins: Instr) -> str:
    return "".join(f"{f} " for f in ins.flags)
