/* expect: E-RECURSION */
#include <stdint.h>
#include "c2mix.h"
static uint32_t fact(uint32_t n) { return n <= 1u ? 1u : n * fact(n - 1u); }
void c2mix_body(void) {
  uint32_t o = 0, n = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("n", &n, 1, sizeof n, 0);
  c2mix_input("n");
  o = fact(n);
  c2mix_done();
}
