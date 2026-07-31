# field_derived: 29 s SIMPLE fold

`fold` in mdtest `field_derived_precise_effect_after_metadata_write`
measured 28.9 s exclusive (58x over the 500 ms simple budget) — an
engine bug independent of the certificate-spelling gap that keeps the
test failing. Re-profile after certificate-spelling-gap lands (the
containment-prover work already collapsed this member's callee
certification >300 s -> 9.7 s, so numbers move).

Also parked here: auto-planned loop-phase certificates should report
source indices the surface proof actually has, so their steps get
locations in profiles.

Repro: cargo run --quiet --bin click-profile -- --time-limit 10m \
  --threshold 500ms mdtests/field_derived_precise_effect_after_metadata_write.md
