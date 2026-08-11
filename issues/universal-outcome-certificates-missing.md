# Universal outcome propositions have no simple certificate lowering

Several proofs fail with:

```text
could not lower the planned smart proof certificate: smart reasoning found a
derivation, but Click has no explicit simple certificate for universal
proposition over CInt32
```

Smart search proves a `forall (k: int32) { ... }` outcome — typically a
loop-summary consequence such as a filled segment or a preserved prefix — but
certificate lowering has no simple steps for universally quantified goals, so
the success cannot become a `SimpleProof`. This blocks `examples/owned-vector`
(also over its budget, see `owned-vector-baseline-misses-project-budget.md`)
and the quarantined mdtests `bubble_sort3_two_pass_sorted.md`,
`composite_resource_vector_fill_loop_snapshot.md`, and `copy3_array_demo.md`.

The related "no explicit simple certificate for that derivation" failures in
`fill_n_segment_invariant.md` and
`shifted_copy_effect_uses_covering_separate.md` also have universally
quantified goals; their scalar siblings (`fill3_array_loop.md`,
`shifted_loop_effect_preserves_prefix.md`) show the same gap for single-cell
loop-effect consequences.

The needed vocabulary is a named simple rule (or small family) that checks a
universal proposition by discharging its bound-variable body from a loop
effect summary or element-wise evidence — with work proportional to the
certificate, not a quantifier search.

## Reproduction

```sh
cargo test --test mdtests -- bubble_sort3_two_pass_sorted
CLICK_EXAMPLE=owned-vector cargo test --test examples
```

## Acceptance criteria

- The quarantined universal-goal mdtests pass and leave quarantine.
- Expansion of a universal outcome contains only named simple steps and
  replays.
- No quantifier instantiation search runs during simple replay.
