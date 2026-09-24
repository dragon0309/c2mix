/* expect: E-DIV */
#include <stdint.h>
#include "c2mix.h"
static void f(uint32_t *out, uint32_t x, uint32_t y) { *out = x / (y | 1u); }
void c2mix_body(void) {
  uint32_t o = 0, x = 0, y = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_register("y", &y, 1, sizeof y, 0);
  c2mix_input("x"); c2mix_input("y");
  f(&o, x, y);
  c2mix_done();
}
