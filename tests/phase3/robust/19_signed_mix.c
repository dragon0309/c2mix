#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* signed and unsigned mixed in one expression */
void c2mix_body(void) {
  int64_t o = 0; int16_t a = 0; uint16_t b = 0;
  c2mix_register("o", &o, 1, sizeof o, 1);
  c2mix_register("a", &a, 1, sizeof a, 1);
  c2mix_register("b", &b, 1, sizeof b, 0);
  c2mix_input("a"); c2mix_input("b");
  o = (int64_t)a * (int64_t)b - (int64_t)(uint64_t)b;
  c2mix_done();
}
