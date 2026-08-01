# Vector loop: slow deterministic close_invariants

`composite_resource_vector_fill_loop_snapshot` now proves successfully after
the certificate-spelling repair. Its remaining quarantine is purely a replay
performance bug:

```
close_invariants class simple: about 2.8 s exclusive
```

The simple-tactic budget is 500 ms. Expanding the former smart `simp` correctly
produced `close_invariants`; adding a resource fold before it did not improve
the timing. Do not hide this with a larger smart budget or another expansion:
profile the deterministic invariant-closing path.

Repro:

```
MDTEST_FILTER=composite_resource_vector_fill_loop_snapshot \
  MDTEST_TIME_LIMIT=2m cargo test --test mdtests -- --nocapture
```
