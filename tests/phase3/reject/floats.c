/* expect: E-FLOAT */
#include <stdint.h>
#include "c2mix.h"
static void f(int32_t *out, int32_t x) { double d = (double)x * 0.5; *out = (int32_t)d; }
void c2mix_body(void) {
  int32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 1);
  c2mix_register("x", &x, 1, sizeof x, 1);
  c2mix_input("x");
  f(&o, x);
  c2mix_done();
}
