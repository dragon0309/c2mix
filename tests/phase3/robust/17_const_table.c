#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* a constant table read at constant indices */
static const uint32_t tbl[16] = {1, 2, 4, 8, 16, 32, 64, 128,
                                 256, 512, 1024, 2048, 4096, 8192, 16384, 32768};
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  uint32_t s = 0;
  for (int i = 0; i < 16; i++) s += tbl[i] & x;
  o = s;
  c2mix_done();
}
