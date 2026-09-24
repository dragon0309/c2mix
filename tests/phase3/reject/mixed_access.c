/* expect: E-MIXED-ACCESS */
#include <stdint.h>
#include "c2mix.h"
static void f(uint32_t *out, uint32_t x) {
  uint32_t v = x;
  uint16_t *p = (uint16_t *)&v;           /* the same storage read at another type */
  *out = (uint32_t)p[0] + (uint32_t)p[1];
}
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  f(&o, x);
  c2mix_done();
}
