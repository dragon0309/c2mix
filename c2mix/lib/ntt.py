"""NTT schedules (spec §4.3, `lib.ntt`), plus the S3 consistency check.

A schedule says, layer by layer, which coefficient block is congruent to the input
modulo which polynomial. After a Cooley–Tukey layer that halves the block length to
`deg`, the block [lo, hi) satisfies

    input ≡ Σ r[j]·x^(j−lo)   (mod q, x^deg − zeta)

The first half of a butterfly pair carries x^deg − ζ, the second x^deg + ζ, because
f = f0 + x^deg·f1 reduces to f0 + ζ·f1 and f0 − ζ·f1 respectively.

Nothing here knows any particular scheme: n, q, the zeta table and R come from the
target's own parameters (G10).
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Block:
    lo: int
    hi: int
    deg: int
    zeta: int          # the modulus is x^deg − zeta (mod q)

    def modulus_coeffs(self, q: int) -> list[int]:
        """x^deg − zeta as a coefficient list, reduced mod q."""
        out = [0] * (self.deg + 1)
        out[self.deg] = 1
        out[0] = (-self.zeta) % q
        return out


class ScheduleError(Exception):
    pass


def ct_schedule(n: int, q: int, zetas, R: int = 1, layers: int | None = None) -> list[list[Block]]:
    """Cooley–Tukey, one entry per layer (S3-checked).

    `zetas` are given in the order the program uses them, in Montgomery form; R turns
    them back (pass R = 1 if they are plain). `layers` limits how far the decomposition
    goes: n//2^layers is the degree of the leaf moduli.
    """
    rinv = pow(R, -1, q) if R != 1 else 1
    layers = layers if layers is not None else n.bit_length() - 1
    out: list[list[Block]] = []
    zetas = list(zetas)
    k = 0
    half = n // 2
    for _ in range(layers):
        blocks: list[Block] = []
        for start in range(0, n, 2 * half):
            if k >= len(zetas):
                raise ScheduleError(f"the schedule needs more than {len(zetas)} zetas")
            z = zetas[k] * rinv % q
            k += 1
            blocks.append(Block(start, start + half, half, z))
            blocks.append(Block(start + half, start + 2 * half, half, (-z) % q))
        out.append(blocks)
        half //= 2
    check_schedule(n, q, out)
    return out


def gs_schedule(n: int, q: int, zetas, R: int = 1, layers: int | None = None) -> list[list[Block]]:
    """Gentleman–Sande (inverse NTT): the same tree, walked from the leaves up."""
    forward = ct_schedule(n, q, zetas, R, layers)
    return list(reversed(forward))


def check_schedule(n: int, q: int, layers: list[list[Block]]) -> None:
    """S3: the leaves multiply out to xⁿ + 1 mod q, the leaf moduli are pairwise
    coprime, and every parent modulus is the product of its two children."""
    if not layers:
        raise ScheduleError("empty schedule")
    for depth, blocks in enumerate(layers):
        if sum(b.hi - b.lo for b in blocks) != n:
            raise ScheduleError(f"layer {depth}: blocks do not cover 0..{n}")
        for a, b in zip(blocks, blocks[1:]):
            if a.hi != b.lo:
                raise ScheduleError(f"layer {depth}: blocks {a} and {b} are not adjacent")

    # parent = product of its two children: (x^d − z)(x^d + z) = x^2d − z²
    for depth in range(len(layers) - 1):
        parents, children = layers[depth], layers[depth + 1]
        for i, parent in enumerate(parents):
            left, right = children[2 * i], children[2 * i + 1]
            if left.deg * 2 != parent.deg or right.deg != left.deg:
                raise ScheduleError(f"layer {depth + 1}: {left} and {right} do not halve {parent}")
            # (x^d − z)(x^d + z) = x^2d − z², so the parent's zeta is the child's squared
            if (left.zeta + right.zeta) % q or (left.zeta * left.zeta - parent.zeta) % q:
                raise ScheduleError(
                    f"layer {depth + 1}: (x^{left.deg} − {left.zeta})(x^{right.deg} − "
                    f"{right.zeta}) is not x^{parent.deg} − {parent.zeta} mod {q}")

    leaves = layers[-1]
    product = [1]
    for b in leaves:
        product = _polymul(product, b.modulus_coeffs(q), q)
    want = [0] * (n + 1)
    want[0], want[n] = 1 % q, 1
    if product != want:
        raise ScheduleError(f"the leaf moduli multiply out to {product}, not x^{n} + 1 mod {q}")
    for i, a in enumerate(leaves):
        for b in leaves[i + 1:]:
            if not _coprime(a.modulus_coeffs(q), b.modulus_coeffs(q), q):
                raise ScheduleError(f"leaf moduli {a} and {b} are not coprime mod {q}")


def _polymul(a: list[int], b: list[int], q: int) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % q
    return out


def _polymod(a: list[int], b: list[int], q: int) -> list[int]:
    """a mod b over F_q (b's leading coefficient must be invertible)."""
    out = [x % q for x in a]
    inv = pow(b[-1], -1, q)
    for i in range(len(out) - 1, len(b) - 2, -1):
        c = out[i] * inv % q
        if c:
            for j in range(len(b)):
                out[i - len(b) + 1 + j] = (out[i - len(b) + 1 + j] - c * b[j]) % q
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def _coprime(a: list[int], b: list[int], q: int) -> bool:
    """Euclid over F_q: the two are coprime when their gcd is a non-zero constant."""
    x, y = [c % q for c in a], [c % q for c in b]
    while not (len(y) == 1 and y[0] == 0):
        x, y = y, _polymod(x, y, q)
    return len(x) == 1 and x[0] != 0
