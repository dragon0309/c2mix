/* c2mix runtime API (spec §4.2).
 *
 * Two implementations answer these four calls: the c2mix executor, which intercepts
 * them by name and needs no body, and runtime/c2mix_rt.c, which is linked into the
 * native binary G2 compares against.
 */
#ifndef C2MIX_H
#define C2MIX_H

#include <stddef.h>

/* Make an object visible to the specification under `name`. */
void c2mix_register(const char *name, void *p, size_t count, size_t elem_size,
                    int is_signed);

/* Turn a registered object's elements into symbolic inputs. */
void c2mix_input(const char *name);

/* A cut: its identity is (tag, k), the k-th time this call is reached. */
void c2mix_cut(int tag);

/* The exit point. */
void c2mix_done(void);

#endif
