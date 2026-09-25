"""Dilithium constants (G10: only under targets/).

As for Kyber, the zeta table is computed from its definition, not copied from
ref/ntt.c: zetas[i] = MONT·ζ^bitrev8(i) mod q, centred, with ζ = 1753 a primitive
512th root of unity mod q. zetas[0] is never read (ntt starts at ++k).
"""
from c2mix.lib.mont import Montgomery

N = 256
Q = 8380417                 # ref/params.h
ROOT = 1753
MONT = Montgomery(Q, 32)
R = MONT.R
LAYERS = 8                  # len = 128 … 1: the leaves are x − ζ (complete NTT)


def _bitrev(i: int, bits: int) -> int:
    return int(format(i, f"0{bits}b")[::-1], 2)


def _centre(v: int) -> int:
    v %= Q
    return v - Q if v > Q // 2 else v


ZETAS = [_centre(MONT.to_montgomery(pow(ROOT, _bitrev(i, 8), Q))) for i in range(N)]
