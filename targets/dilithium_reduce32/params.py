"""Dilithium constants (G10: only under targets/)."""
Q = 8380417                 # ref/params.h
R = 1 << 32                 # the Montgomery radix
MONT_BOUND = Q * (1 << 31)  # montgomery_reduce's stated input bound

# reduce32's own comment states only the upper end, "a <= 2^31 - 2^22 - 1", which is the
# condition for `a + (1 << 22)` not to overflow int32 — not a bound on |a|. Leaving the
# lower end at -2^31 makes the post-condition false, and G5 said so: a = -2143289344
# gives r = -6283009, one past the bound the same comment promises.
#
# That input is the only one. Writing r = t*8191 + s with t = floor((a + 2^22) / 2^23),
# s = a - t*2^23 in [-2^22, 2^22 - 1] and 2^23 - Q = 8191: for t >= -254,
# r >= -254*8191 - 2^22 > -6283008; at t = -255, r = -2088705 + s, which fails only for
# s = -2^22, i.e. a = -255*2^23 - 2^22 = -(2^31 - 2^22); at t = -256, a = -2^31 + s
# forces s >= 0 inside int32, so r >= -2096896 (reduce32(INT32_MIN) = -2096896). The
# top end is exact too: a = 2^31 - 2^22 - 1 gives t = 255, s = 2^22 - 1, r = 6283008.
# An exhaustive run over [-2^31, 2^31 - 2^22 - 1] agrees: one failure, at -(2^31 - 2^22).
# So the symmetric bound below is the largest interval around 0 on which the
# post-condition holds; it cannot be widened by one at either end.
#
# Every call site is far inside it. reduce32 is only reached through poly_reduce
# (freeze calls it too, but nothing calls freeze), and poly_reduce is called six times
# in ref/sign.c. Three of them (sign.c:51, 140, 339) take the output of
# polyvec_matrix_pointwise_montgomery, which sums L values each bounded by
# montgomery_reduce's |r| < Q, so |a| < L*Q, or (L+1)*Q at sign.c:339 where a further
# pointwise product is subtracted. For the vendored DILITHIUM_MODE 2 (L = 4) that is at
# most 5Q ~ 2^25.3, 51x inside the bound below; mode 5 (L = 7) reaches 8Q = 2^26, still
# 32x inside. The other three (sign.c:160, 169, 176) take values computed from the
# output of invntt_tomont, and that is in the phase 5 held-out set (§9), so its bound
# is not something to look up here.
#
# So the bound stays the general one rather than the call sites': it is the stronger
# theorem, it cannot be relaxed, and it needs nothing from the held-out set. Phase 4's
# "Dilithium 的界線由規格模組依 montgomery_reduce 的輸出界推導" is about the ntt target,
# where the bounds really do have to be derived that way.
RED32_HI = (1 << 31) - (1 << 22) - 1
RED32_OUT = 6283008
