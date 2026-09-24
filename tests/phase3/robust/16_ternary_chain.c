#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* nested conditional expressions */
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  o = (x & 1u) ? ((x & 2u) ? 10u : 20u) : ((x & 4u) ? 30u : 40u);
  c2mix_done();
}
