#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* a read of storage that was never written */
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  uint32_t scratch[2];
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  scratch[1] = x;
  o = scratch[0] + scratch[1];        /* scratch[0] was never written */
  c2mix_done();
}
