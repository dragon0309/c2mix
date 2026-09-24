#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* a struct passed by value */
struct pair { uint32_t a; uint32_t b; };
static uint32_t sum(struct pair p) { return p.a + p.b; }
void c2mix_body(void) {
  uint32_t o = 0, x = 0, y = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_register("y", &y, 1, sizeof y, 0);
  c2mix_input("x"); c2mix_input("y");
  struct pair p = {x, y};
  o = sum(p);
  c2mix_done();
}
