#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* bit-fields */
struct flags { unsigned a : 3; unsigned b : 5; };
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  struct flags f = {0, 0};
  f.a = x & 7u;
  f.b = (x >> 3) & 31u;
  o = f.a + f.b;
  c2mix_done();
}
