"""fiat-crypto P-256 constants (G10: only under targets/)."""
W = 64                                    # machine word size
RADIX = 1 << W
P = 2**256 - 2**224 + 2**192 + 2**96 - 1  # the p256 prime
