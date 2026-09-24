#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* memcpy of a whole array */
void c2mix_body(void) {
  uint32_t a[4] = {0}, b[4] = {0};
  c2mix_register("a", a, 4, sizeof a[0], 0);
  c2mix_register("b", b, 4, sizeof b[0], 0);
  c2mix_input("a");
  __builtin_memcpy(b, a, sizeof a);
  b[0] ^= 1u;
  c2mix_done();
}
