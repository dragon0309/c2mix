"""fiat-crypto curve25519 constants (G10: only under targets/)."""
LIMBS = 5
RADIX_BITS = 51                            # eval z = Σ z[i]·2^(51·i), unsaturated
P = 2**255 - 19
LOOSE = 0x18000000000000                   # fiat's bound on each input limb (inclusive)
TIGHT = 0x8000000000000                    # and on each output limb (inclusive)
