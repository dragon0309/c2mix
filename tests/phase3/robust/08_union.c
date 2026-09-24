#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* type punning through a union */
union u { uint32_t w; uint8_t b[4]; };
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  union u v; v.w = x;
  o = v.b[0];
  c2mix_done();
}
