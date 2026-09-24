#include <stdint.h>

#define KYBER_Q 3329
#define QINV -3327 /* q^-1 mod 2^16 */

/* From 02_montgomery.c, itself pq-crystals/kyber ref/reduce.c. Verbatim. */
int16_t montgomery_reduce(int32_t a) {
  int16_t t;
  t = (int16_t)a * QINV;
  t = (a - (int32_t)t * KYBER_Q) >> 16;
  return t;
}
