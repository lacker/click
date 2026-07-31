# field_derived's 29 s SIMPLE fold

Status: open (small; measure again after separation-containment-prover lands)
Claimed:

`fold` in `field_derived_precise_effect_after_metadata_write` takes
28.9 s exclusive — 58x over the simple budget, an engine bug
independent of the closer-replay item. Note: the containment-prover
fix collapsed the callee's certification >300 s -> 9.7 s in probes, so
re-profile this member after that lands before optimizing anything.

Also parked here: auto-planned loop-phase certificates should report
source indices the surface proof actually has, so their steps get
locations in profiles.

Repro:
```
cargo run --quiet --bin click-profile -- --time-limit 10m --threshold 500ms \
  mdtests/field_derived_precise_effect_after_metadata_write.md
```
