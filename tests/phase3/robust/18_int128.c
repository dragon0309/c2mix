#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* a 128-bit product */
void c2mix_body(void) {
  uint64_t lo = 0, hi = 0, a = 0, b = 0;
  c2mix_register("lo", &lo, 1, sizeof lo, 0);
  c2mix_register("hi", &hi, 1, sizeof hi, 0);
  c2mix_register("a", &a, 1, sizeof a, 0);
  c2mix_register("b", &b, 1, sizeof b, 0);
  c2mix_input("a"); c2mix_input("b");
  unsigned __int128 p = (unsigned __int128)a * b;
  lo = (uint64_t)p;
  hi = (uint64_t)(p >> 64);
  c2mix_done();
}
