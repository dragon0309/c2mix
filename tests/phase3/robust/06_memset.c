#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* memset with a constant length */
void c2mix_body(void) {
  uint8_t a[8] = {0};
  uint32_t x = 0;
  c2mix_register("a", a, 8, sizeof a[0], 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  __builtin_memset(a, 0, sizeof a);
  a[0] = (uint8_t)x;
  c2mix_done();
}
