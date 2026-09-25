"""Lowering rules L1–L14 (spec §6.3).

Each IR instruction becomes statements in two models:
  * the range model  — bit-vectors, exactly the program semantics;
  * the algebraic model — equations over ℤ about ⟦v⟧, the integers the bit-vectors
    stand for; these are what the mix VC's algebraic section asserts.
plus, for EXACT decisions, a safety obligation for the range VC (§7.4).

Every algebraic statement must be implied by the range statements and the safety
obligations — that is rule lemma A1.1, and `lemmas.py` generates it from this code.
"""
from __future__ import annotations

from ..ir import intervals as iv
from ..ir.ops import Instr, Program, Value
from . import encode as E
from . import idioms
from .encode import Encoder, Segment

W_ALG_FREE = "W-ALG-FREE"


class LoweringError(Exception):
    pass


def lower(prog: Program, analysis: iv.Analysis | None = None, mode: str = E.ALIAS,
          pre: dict | None = None, force_split: bool = False,
          span: tuple[int, int] | None = None, enc: Encoder | None = None,
          copy_alias: bool = False) -> Segment:
    """Lower a program, or with `span` just the instructions of one segment; values
    defined earlier are declared but not defined, which is what makes them the
    segment's inputs (§7.1)."""
    analysis = analysis or iv.analyze(prog, pre, force_split, span)
    defined = {v.name: v.signed for v in prog.values()}
    enc = enc or Encoder(Segment(), mode, analysis.intervals, defined, copy_alias=copy_alias)
    if not enc.intervals:
        enc.intervals = analysis.intervals
    enc.defined_signed = {**defined, **enc.defined_signed}
    seg = enc.seg
    lo, hi = span or (0, len(prog.instrs))
    for ins in prog.instrs:                      # constants are inlined everywhere (L1)
        if ins.op == "const":
            enc.set_const(ins.result, ins.value)
    if span is None:
        for v in prog.inputs:
            enc.declare(v)
    definitions = idioms.defs(prog)
    for idx, ins in enumerate(prog.instrs[lo:hi], start=lo):
        _lower_instr(ins, idx, enc, seg, analysis, definitions)
    return seg


def _lower_instr(ins: Instr, idx: int, enc: Encoder, seg: Segment, an: iv.Analysis,
                 definitions: dict | None = None) -> None:
    op = ins.op
    decision = an.decisions.get(idx)
    note = lambda rule, extra=None: seg.notes.append(
        {"index": idx, "op": op, "rule": rule, "decision": decision, **(extra or {})})

    if op == "const":                                                   # L1
        return note("L1")
    if op == "marker":                                                  # L14
        return note("L14", {"tag": ins.tag})

    r = ins.result
    if op in ("add", "sub", "neg"):                                     # L3 / L3′
        return _lower_addsub(ins, enc, seg, decision, note)
    if op == "mul":                                                     # L4 / L4′
        return _lower_mul(ins, enc, seg, decision, note)
    if op == "shl":                                                     # L6 (via L4)
        return _lower_shl(ins, enc, seg, decision, note)
    if op in ("ashr", "lshr"):                                          # L7
        return _lower_shr(ins, enc, seg, note)
    if op in ("sext", "zext"):                                          # L5 / L8
        kind = "sign_extend" if op == "sext" else "zero_extend"
        a = ins.args[0]
        seg.bv.append(["=", r.name, E.extend(kind, r.width - a.width, enc.bv(a))])
        enc.declare(r)
        _copy(enc, seg, r, r.signed, enc.atom(a))
        return note("L8")
    if op == "extract":                                                 # L9 / L9′ / L11
        return _lower_extract(ins, enc, seg, decision, note)
    if op == "and":
        site = iv.mask_site(ins, an.consts)
        if site is not None:                                            # L9m
            return _lower_mask(ins, site, enc, seg, note)
        return _lower_free(ins, enc, seg, note)                         # L13
    if op == "or":
        site = idioms.mask_select(ins, definitions or {}, an.masks)
        if site is not None:                                            # L12 (mask form)
            return _lower_mask_select(ins, site, enc, seg, note)
        return _lower_free(ins, enc, seg, note)                         # L13
    if op == "xor":                                                     # L13
        return _lower_free(ins, enc, seg, note)
    if op == "not":                                                     # L13n
        a = ins.args[0]
        seg.bv.append(["=", r.name, ["bvnot", enc.bv(a)]])
        enc.declare(r)
        if r.signed:
            rhs = E.PSub(E.PInt(-1), E.PConst(enc.atom(a, signed=True)))
        else:
            rhs = E.PSub(E.PInt((1 << r.width) - 1), E.PConst(enc.atom(a, signed=False)))
        seg.alg.append(E.eqP(E.PConst(enc.atom(r)), rhs))
        return note("L13n")
    if op == "cmp":                                                     # L13
        return _lower_cmp(ins, enc, seg, note)
    if op == "ite":                                                     # L12
        return _lower_ite(ins, enc, seg, note)
    raise LoweringError(f"no rule for {ins}")


# ---------------------------------------------------------------- helpers
def _widen(enc: Encoder, v: Value, by: int, signed: bool):
    kind = "sign_extend" if signed else "zero_extend"
    return E.extend(kind, by, enc.bv(v))


def _in_type(term, term_width: int, target: Value, read_signed: bool | None = None):
    """QF_BV obligation: the value of `term`, read with `read_signed` (default: the
    target's signedness), lies in target's type range. Comparisons happen at
    term_width (§7.4)."""
    if target.signed if read_signed is None else read_signed:
        return ["and",
                ["bvsle", E.bv_const(target.lo, term_width), term],
                ["bvsle", term, E.bv_const(target.hi, term_width)]]
    return ["bvule", term, E.bv_const(target.hi, term_width)]


def _copy(enc: Encoder, seg: Segment, r: Value, signed: bool, atom) -> None:
    """⟦r⟧ (read `signed`) = the integer `atom` stands for. With copy aliasing r simply
    takes that atom (Encoder.alias); otherwise the equation is stated."""
    if enc.copy_alias:
        enc.alias(r, signed, atom)
    else:
        seg.alg.append(E.eqP(E.PConst(enc.read(r, signed)), E.PConst(atom)))


def _split_eq(whole, parts, sum_first: bool = False):
    """⟦whole⟧ = Σ ⟦part⟧·2^shift, as one algebraic statement. `sum_first` puts the
    sum on the left, which is how the golden files write the L4′ product split."""
    terms = [E.PMul(E.PConst(a), E.PInt(1 << s)) if s else E.PConst(a) for a, s in parts]
    total = E.psum(terms)
    return E.eqP(total, whole) if sum_first else E.eqP(whole, total)


# ---------------------------------------------------------------- rules
def _lower_addsub(ins, enc: Encoder, seg: Segment, decision, note):
    r, a = ins.result, ins.args[0]
    b = ins.args[1] if ins.op != "neg" else None
    signed = a.signed
    bvop = {"add": "bvadd", "sub": "bvsub", "neg": "bvneg"}[ins.op]
    seg.bv.append(["=", r.name, [bvop, enc.bv(a)] + ([enc.bv(b)] if b is not None else [])])
    enc.declare(r)
    ia = E.PConst(enc.read(a, signed))
    exact = {"add": lambda: E.PAdd(ia, E.PConst(enc.read(b, signed))),
             "sub": lambda: E.PSub(ia, E.PConst(enc.read(b, signed))),
             "neg": lambda: E.PNeg(ia)}[ins.op]()
    # a − b and −a can be negative even for unsigned operands, so the widened result
    # is read as signed there; the golden files write that borrow as −carry·2^w.
    wide_signed = signed or ins.op in ("sub", "neg")
    if decision == iv.EXACT:                                            # L3
        seg.alg.append(E.eqP(E.PConst(enc.read(r, signed)), exact))
        wide = [_widen(enc, a, 1, signed)] + ([_widen(enc, b, 1, signed)] if b is not None else [])
        seg.safety.append(_in_type([bvop] + wide, r.width + 1, r, wide_signed))
        return note("L3")
    # L3′: compute at w+1 and split off the top bit (L5 + L9-SPLIT)
    w = r.width
    wide = [_widen(enc, a, 1, signed)] + ([_widen(enc, b, 1, signed)] if b is not None else [])
    h = enc.witness("h", 1, wide_signed)
    seg.bv.append(["=", h.name, E.extract(w, w, [bvop] + wide)])
    seg.alg.append(_split_eq(exact, [(enc.atom(h), w), (enc.read(r, False), 0)]))
    return note("L3'", {"witness": h.name})


def _lower_mul(ins, enc: Encoder, seg: Segment, decision, note):
    r, a, b = ins.result, ins.args[0], ins.args[1]
    signed = a.signed
    w = r.width
    seg.bv.append(["=", r.name, ["bvmul", enc.bv(a), enc.bv(b)]])
    enc.declare(r)
    prod = E.PMul(E.PConst(enc.read(a, signed)), E.PConst(enc.read(b, signed)))
    if decision == iv.EXACT:                                            # L4
        seg.alg.append(E.eqP(E.PConst(enc.read(r, signed)), prod))
        wide = ["bvmul", _widen(enc, a, w, signed), _widen(enc, b, w, signed)]
        seg.safety.append(_in_type(wide, 2 * w, r))
        return note("L4")
    # L4′: the golden mulH/mulL split
    wide = ["bvmul", _widen(enc, a, w, signed), _widen(enc, b, w, signed)]
    h = enc.witness("h", w, signed)
    seg.bv.append(["=", h.name, E.extract(2 * w - 1, w, wide)])
    seg.alg.append(_split_eq(prod, [(enc.read(r, False), 0), (enc.atom(h), w)], sum_first=True))
    return note("L4'", {"witness": h.name})


def _lower_shl(ins, enc: Encoder, seg: Segment, decision, note):
    r, a, k = ins.result, ins.args[0], ins.k
    signed, w = a.signed, r.width
    seg.bv.append(["=", r.name, ["bvshl", enc.bv(a), E.bv_const(k, w)]])
    enc.declare(r)
    scaled = E.PMul(E.PConst(enc.read(a, signed)), E.PInt(1 << k))
    if decision == iv.EXACT:                                            # L6 via L4
        seg.alg.append(E.eqP(E.PConst(enc.read(r, signed)), scaled))
        wide = ["bvshl", _widen(enc, a, k, signed), E.bv_const(k, w + k)]
        seg.safety.append(_in_type(wide, w + k, r))
        return note("L6")
    if k == 0:
        seg.alg.append(E.eqP(E.PConst(enc.read(r, signed)), scaled))
        return note("L6")
    wide = ["bvshl", _widen(enc, a, k, signed), E.bv_const(k, w + k)]
    h = enc.witness("h", k, signed)
    seg.bv.append(["=", h.name, E.extract(w + k - 1, w, wide)])
    seg.alg.append(_split_eq(scaled, [(enc.atom(h), w), (enc.read(r, False), 0)]))
    return note("L6'", {"witness": h.name})


def _lower_shr(ins, enc: Encoder, seg: Segment, note):                  # L7
    r, a, k = ins.result, ins.args[0], ins.k
    signed = ins.op == "ashr"
    seg.bv.append(["=", r.name, ["bvashr" if signed else "bvlshr", enc.bv(a), E.bv_const(k, a.width)]])
    enc.declare(r)
    split = seg.split_at.get((a.name, k))
    if enc.copy_alias and split is not None and a.signed == signed:
        # a was already split at bit k by a mask (L9m): x = h·2^k + low. The shift is
        # that same h (floor division, read the way the shift reads a), so it takes
        # h's atom; the low part is the mask's result, which is where a hint about the
        # low bits (the Montgomery "low half is zero") now looks.
        high, low = split
        enc.alias(r, signed, enc.atom(high, signed))
        seg.shifted.append(a)
        return note("L7", {"witness": low.name, "reuses": "L9m"})
    parts = [(enc.read(r, signed), k)]
    if k:
        low = enc.witness("l", k, False)
        seg.bv.append(["=", low.name, E.extract(k - 1, 0, enc.bv(a))])
        parts.append((enc.atom(low), 0))
    seg.alg.append(_split_eq(E.PConst(enc.read(a, signed)), parts))
    seg.shifted.append(a)
    return note("L7", {"witness": low.name if k else None})


def _lower_extract(ins, enc: Encoder, seg: Segment, decision, note):
    r, x = ins.result, ins.args[0]
    hi, lo, W = ins.hi, ins.lo, x.width
    seg.bv.append(["=", r.name, E.extract(hi, lo, enc.bv(x))])
    enc.declare(r)
    if lo == 0 and hi == W - 1:                                         # identity
        _copy(enc, seg, r, x.signed, enc.read(x, x.signed))
        return note("L9")
    if decision == iv.EXACT and lo == 0:                                # L9
        _copy(enc, seg, r, r.signed, enc.read(x, r.signed))
        seg.safety.append(_in_type(enc.bv(x), W, r))
        return note("L9")
    # L9′ / L11: x splits into (high, this field, low); the top field carries x's
    # signedness, the lower fields are unsigned.
    parts, wit = [], []
    if hi < W - 1:
        h = enc.witness("h", W - 1 - hi, x.signed)
        seg.bv.append(["=", h.name, E.extract(W - 1, hi + 1, enc.bv(x))])
        parts.append((enc.atom(h), hi + 1))
        wit.append(h.name)
        parts.append((enc.read(r, False), lo))
    else:
        parts.append((enc.read(r, x.signed), lo))
    if lo > 0:
        low = enc.witness("l", lo, False)
        seg.bv.append(["=", low.name, E.extract(lo - 1, 0, enc.bv(x))])
        parts.append((enc.atom(low), 0))
        wit.append(low.name)
    seg.alg.append(_split_eq(E.PConst(enc.read(x, x.signed)), parts))
    if lo == 0:
        _record_split(seg, x, r, hi + 1)
    return note("L9'" if lo == 0 else "L11", {"witness": wit})


def _lower_mask(ins, site, enc: Encoder, seg: Segment, note):           # L9m
    r = ins.result
    k, mask_index = site
    const, x = ins.args[mask_index], ins.args[1 - mask_index]
    W = x.width
    seg.bv.append(["=", r.name, ["bvand", enc.bv(x), enc.bv(const)]])
    enc.declare(r)
    h = enc.witness("h", W - k, x.signed)
    seg.bv.append(["=", h.name, E.extract(W - 1, k, enc.bv(x))])
    seg.alg.append(_split_eq(E.PConst(enc.read(x, x.signed)),
                             [(enc.atom(h), k), (enc.read(r, False), 0)]))
    _record_split(seg, x, r, k)
    seg.split_at[(x.name, k)] = (h, r)
    seg.shifted.append(x)
    return note("L9m", {"witness": h.name})


def _record_split(seg: Segment, src: Value, low: Value, width: int) -> None:
    """Remember what a SPLIT narrowing threw away: ⟦src⟧ − ⟦low⟧, each read its own way.
    That quantity is a multiple of 2^width, and two of them being equal is often the one
    fact an algebraic proof is missing (hint H5, §6.4)."""
    seg.splits.append({"src": src, "low": low, "width": width})


def _lower_free(ins, enc: Encoder, seg: Segment, note):                 # L13
    r = ins.result
    bvop = {"and": "bvand", "or": "bvor", "xor": "bvxor"}[ins.op]
    seg.bv.append(["=", r.name, [bvop, enc.bv(ins.args[0]), enc.bv(ins.args[1])]])
    enc.declare(r)
    return note("L13", {"warning": W_ALG_FREE})


def _lower_cmp(ins, enc: Encoder, seg: Segment, note):                  # L13
    r, a, b = ins.result, ins.args[0], ins.args[1]
    pred = {"eq": "=", "ne": "distinct", "ult": "bvult", "ule": "bvule", "ugt": "bvugt",
            "uge": "bvuge", "slt": "bvslt", "sle": "bvsle", "sgt": "bvsgt", "sge": "bvsge"}[ins.pred]
    seg.bv.append(["=", r.name, ["ite", [pred, enc.bv(a), enc.bv(b)], "#b1", "#b0"]])
    enc.declare(r)
    return note("L13", {"warning": W_ALG_FREE})


def _lower_mask_select(ins, site, enc: Encoder, seg: Segment, note):    # L12, mask form
    """`r = (m & a) | (~m & b)`: the same equation as the `ite` form, with the mask's
    low bit as the condition. m being all ones or all zero is the safety obligation."""
    r = ins.result
    m, a, b = site
    seg.bv.append(["=", r.name, ["bvor", enc.bv(ins.args[0]), enc.bv(ins.args[1])]])
    enc.declare(r)
    c = enc.witness("c", 1, False)
    seg.bv.append(["=", c.name, E.extract(0, 0, enc.bv(m))])
    seg.safety.append(["or", ["=", enc.bv(m), E.bv_const(0, m.width)],
                       ["=", enc.bv(m), E.bv_const((1 << m.width) - 1, m.width)]])
    signed = r.signed
    ca, cb, cc = enc.read(a, signed), enc.read(b, signed), enc.atom(c)
    seg.alg.append(E.eqP(E.PConst(enc.read(r, signed)),
                         E.PAdd(E.PConst(cb), E.PMul(E.PConst(cc),
                                                     E.PSub(E.PConst(ca), E.PConst(cb))))))
    seg.alg.append(E.eqP(E.PMul(E.PConst(cc), E.PConst(cc)), E.PConst(cc)))
    return note("L12", {"form": "mask", "witness": c.name})


def _lower_ite(ins, enc: Encoder, seg: Segment, note):                  # L12
    r, c, a, b = ins.result, *ins.args
    seg.bv.append(["=", r.name, ["ite", ["=", enc.bv(c), "#b1"], enc.bv(a), enc.bv(b)]])
    enc.declare(r)
    signed = r.signed
    ca, cb, cc = enc.read(a, signed), enc.read(b, signed), enc.atom(c, signed=False)
    seg.alg.append(E.eqP(E.PConst(enc.read(r, signed)),
                         E.PAdd(E.PConst(cb), E.PMul(E.PConst(cc),
                                                     E.PSub(E.PConst(ca), E.PConst(cb))))))
    seg.alg.append(E.eqP(E.PMul(E.PConst(cc), E.PConst(cc)), E.PConst(cc)))
    return note("L12")
