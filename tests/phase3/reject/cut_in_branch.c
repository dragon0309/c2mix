/* expect: E-SYMBOLIC-BRANCH — a cut inside an input-dependent branch cannot be merged */
#include <stdint.h>
#include "c2mix.h"
static void f(uint32_t *out, uint32_t c) {
  if (c & 1u) c2mix_cut(1);
  *out = c;
}
void c2mix_body(void) {
  uint32_t o = 0, c = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("c", &c, 1, sizeof c, 0);
  c2mix_input("c");
  f(&o, c);
  c2mix_done();
}
