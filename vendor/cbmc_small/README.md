# cbmc_small (transcribed)

Source: `extend_z3/working/cbmc_small/0*.c` (F7). Those files are CBMC harnesses:
the computation sits inside `main`, wrapped in `__CPROVER_assume` / `__CPROVER_assert`
and fed by `nondet_*()`. c2mix cannot use that shape — it needs a plain C function it
can call from its own harness (§4.2).

Each file here keeps the **computation verbatim** and replaces only the CBMC scaffolding:
`nondet_*()` values become parameters, `__CPROVER_assume` becomes the specification's
pre-condition, and `__CPROVER_assert` becomes its post-condition. Nothing else changed.

This corpus is *not* confirmed correct (§2.1); it is only a source of C test programs,
and A3.5 compares against its `cv` output as a report, never as an expected result.
