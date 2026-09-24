"""Dilithium constants (G10: only under targets/)."""
Q = 8380417                 # ref/params.h
R = 1 << 32                 # the Montgomery radix
MONT_BOUND = Q * (1 << 31)  # montgomery_reduce's stated input bound

# reduce32's comment states only the upper end, "a <= 2^31 - 2^22 - 1"; the domain is
# the symmetric one. G5 is what established that: with the lower end left at −2^31,
# a = −2143289344 gives r = −6283009, one past the bound the same comment promises.
RED32_HI = (1 << 31) - (1 << 22) - 1
RED32_OUT = 6283008
