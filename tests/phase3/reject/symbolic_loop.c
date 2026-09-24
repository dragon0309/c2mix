/* expect: E-SYMBOLIC-LOOP */
#include <stdint.h>
#include "c2mix.h"
static void f(uint32_t *out, uint32_t n) {
  uint32_t s = 0;
  for (uint32_t i = 0; i < n; i++) s += i;
  *out = s;
}
void c2mix_body(void) {
  uint32_t o = 0, n = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("n", &n, 1, sizeof n, 0);
  c2mix_input("n");
  f(&o, n);
  c2mix_done();
}
