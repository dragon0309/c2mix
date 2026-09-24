#include <stdint.h>

/* From 04_loop_mul.c: shift-and-add multiplication with a 4-bit multiplier.
 * The loop body is verbatim; `acc` became an out-parameter and the
 * `__CPROVER_assume(k < 16)` became the specification's pre-condition.
 * The `if` inside the loop is input-dependent, so the executor has to merge (§5.5). */
void loop_mul(uint16_t *acc_out, uint16_t x, uint16_t k) {
  uint16_t acc = 0;
  for (int i = 0; i < 4; i++) {
    if ((k >> i) & 1)
      acc += (uint16_t)(x << i);
  }
  *acc_out = acc;
}
