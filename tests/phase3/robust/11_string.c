#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* a string literal walked by a constant-bounded loop */
static uint32_t len(const char *s) { uint32_t n = 0; while (s[n]) n++; return n; }
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  o = len("c2mix") + x;
  c2mix_done();
}
