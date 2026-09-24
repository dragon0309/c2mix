"""Dilithium constants (G10: only under targets/)."""
Q = 8380417                 # ref/params.h
R = 1 << 32                 # the Montgomery radix
MONT_BOUND = Q * (1 << 31)  # montgomery_reduce's stated input bound
RED32_HI = (1 << 31) - (1 << 22)    # reduce32 requires a <= 2³¹ − 2²² − 1
RED32_OUT = 6283008                 # the bound its comment states
