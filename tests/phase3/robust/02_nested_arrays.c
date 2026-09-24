#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* a two-dimensional array with constant indices */
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  uint32_t grid[3][4] = {{0}};
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 4; j++) grid[i][j] = x + (uint32_t)(i * 4 + j);
  o = grid[2][3] ^ grid[0][0];
  c2mix_done();
}
