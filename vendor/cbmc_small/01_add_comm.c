#include <stdint.h>

/* From 01_add_comm.c: 8-bit wrap-around addition commutes.
 * `__CPROVER_assert(s == (uint8_t)(y + x))` becomes the two outputs a spec compares. */
void add_comm(uint8_t *s, uint8_t *t, uint8_t x, uint8_t y) {
  *s = x + y;
  *t = y + x;
}
