#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* three levels of inlining */
static uint32_t a3(uint32_t x) { return x ^ 3u; }
static uint32_t a2(uint32_t x) { return a3(x) + 2u; }
static uint32_t a1(uint32_t x) { return a2(x) * 5u; }
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  o = a1(x);
  c2mix_done();
}
