#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* a function pointer with a constant target */
static uint32_t inc(uint32_t x) { return x + 1u; }
static uint32_t dbl(uint32_t x) { return x << 1; }
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  uint32_t (*f)(uint32_t) = (x & 0u) ? dbl : inc;
  o = f(x);
  c2mix_done();
}
