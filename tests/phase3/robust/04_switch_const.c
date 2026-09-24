#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* switch on a constant */
static uint32_t pick(uint32_t x, int which) {
  switch (which) {
  case 0: return x + 1u;
  case 1: return x << 1;
  case 2: return x ^ 0xFFFFu;
  default: return x;
  }
}
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  o = pick(x, 0) + pick(x, 1) + pick(x, 2) + pick(x, 7);
  c2mix_done();
}
