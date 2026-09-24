#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* a shift by an input-dependent amount */
void c2mix_body(void) {
  uint32_t o = 0, x = 0, n = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_register("n", &n, 1, sizeof n, 0);
  c2mix_input("x"); c2mix_input("n");
  o = x << (n & 31u);
  c2mix_done();
}
