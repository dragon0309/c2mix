#include <stdint.h>
#include <stddef.h>
#include "c2mix.h"
/* varargs */
#include <stdarg.h>
static uint32_t total(int n, ...) {
  va_list ap; va_start(ap, n);
  uint32_t s = 0;
  for (int i = 0; i < n; i++) s += (uint32_t)va_arg(ap, unsigned);
  va_end(ap);
  return s;
}
void c2mix_body(void) {
  uint32_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 0);
  c2mix_register("x", &x, 1, sizeof x, 0);
  c2mix_input("x");
  o = total(2, x, 7u);
  c2mix_done();
}
