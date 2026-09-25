"""Kyber constants (G10: only under targets/).

The zeta table is computed here from its definition rather than copied from ref/ntt.c:
zetas[i] = MONT·ζ^bitrev7(i) mod q, centred, with ζ = 17 the primitive 256th root of
unity (the generator program in the comment at the top of ref/ntt.c). A specification
that read the table out of the source would agree with a wrong table.
"""
from c2mix.lib.mont import Montgomery

N = 256
Q = 3329                    # KYBER_Q
ROOT = 17                   # KYBER_ROOT_OF_UNITY
MONT = Montgomery(Q, 16)
R = MONT.R
LAYERS = 7                  # len = 128 … 2: the leaves are x² − ζ (incomplete NTT)


def _bitrev(i: int, bits: int) -> int:
    return int(format(i, f"0{bits}b")[::-1], 2)


def _centre(v: int) -> int:
    v %= Q
    return v - Q if v > Q // 2 else v


ZETAS = [_centre(MONT.to_montgomery(pow(ROOT, _bitrev(i, 7), Q))) for i in range(128)]
