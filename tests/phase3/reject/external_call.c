/* expect: E-EXTERNAL-CALL */
#include <stdint.h>
#include "c2mix.h"
extern uint32_t c2mix_undefined_helper(uint32_t);
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  o = c2mix_undefined_helper(x);
  c2mix_done();
}
