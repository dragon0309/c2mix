/* expect: E-DYN-INDEX */
#include <stdint.h>
#include "c2mix.h"
static const int16_t tbl[8] = {1, 2, 3, 4, 5, 6, 7, 8};
static void f(int16_t *out, int32_t i) { *out = tbl[i & 7]; }
void c2mix_body(void) {
  int16_t o = 0; int32_t i = 0;
  c2mix_register("o", &o, 1, sizeof o, 1);
  c2mix_register("i", &i, 1, sizeof i, 1);
  c2mix_input("i");
  f(&o, i);
  c2mix_done();
}
