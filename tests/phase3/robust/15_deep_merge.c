#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* nested input-dependent branches */
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  uint32_t v = x;
  if (v & 1u) { if (v & 2u) { if (v & 4u) v += 1u; else v += 2u; } else v += 3u; }
  else { if (v & 8u) v += 4u; else v += 5u; }
  o = v;
  c2mix_done();
}
