#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* a loop written with goto */
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  uint32_t acc = 0;
  int i = 0;
loop:
  acc += x + (uint32_t)i;
  if (++i < 5) goto loop;
  o = acc;
  c2mix_done();
}
