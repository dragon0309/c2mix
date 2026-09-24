/* expect: E-VECTOR */
#include <stdint.h>
#include "c2mix.h"
typedef int16_t v8 __attribute__((vector_size(16)));
void c2mix_body(void) {
  int16_t o = 0, x = 0;
  c2mix_register("o", &o, 1, sizeof o, 1);
  c2mix_register("x", &x, 1, sizeof x, 1);
  c2mix_input("x");
  v8 a = {x, x, x, x, x, x, x, x};
  v8 b = a + a;
  o = b[0];
  c2mix_done();
}
