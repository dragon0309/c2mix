#include <stdint.h>

/* The selection fiat-crypto writes as a mask (`fiat_p256_cmovznz_u64`), written the two
 * other ways a C programmer would: with `if`/`else`, and with `?:`. Both conditions
 * depend on the input, so the executor has to find the join point and merge (§5.5).
 * This is A3.9's subject. */
void cmov_branch(uint64_t *out1, uint64_t *out2, uint8_t c, uint64_t a, uint64_t b) {
  if (c)
    *out1 = a;
  else
    *out1 = b;
  *out2 = c ? b : a;
}
