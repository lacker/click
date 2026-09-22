# The annotation quantifier counter is raised from foreign variables

P1. Fresh identifiers must come from a range owned by their producer; the
quantifier counter's next value is partly determined by captured values it
does not own.

## What was found

The annotation lowerers mint quantifier binders by growing
`next_quantifier_variable` (`src/surface/lowering/annotations.rs:2657`,
`2743`, `2833`, `2882`, `3616`, `4111`, `4683`) with only u64-saturation
guards — unlike the kernel counter's explicit band ceiling
(`src/kernel/primitives/derivations.rs:1482`). Worse, two sites *raise* the
counter from foreign sources: `annotations.rs:1186-1199` and
`:1324-1328` set
`next_quantifier_variable = max(variable.0 + 1)` over **every variable
occurring in captured Integer values**. A captured Integer value that
carries an execution-issued identity (loop-havoc or join variables minted
in the execution band `1_000_000..2_000_000` — the capture route
`capture_spec_integer_value`, `src/kernel/spec.rs:128-183`, reads values
out of live state where those identities are not verifiably dead) lifts the
counter into the execution band: the next quantifier binder mints inside a
band whose future mints are still being handed out by the kernel. Two
different producers can then own the same identity — binder-vs-binder
capture across producers, the invariant
`the_match_binder_range_is_disjoint_from_every_other_producer` guards
everywhere else.

This is the same invariant family as
`bugs/spec-fold-binders-collide-with-quantifier-band.md` (the fold band
overlapping this counter's static base) and additionally shows the counter
being *raised into* other producers' territory at runtime.

## Intended regression

A lowering-level test capturing an Integer value that mentions an
execution-band `Variable` and then elaborating an annotation with a
quantifier: the minted binder identity must stay outside the execution
band (refused, or a reserved-band rehash), and a runtime Assertions-shaped
shared-id checker (like `the_match_binder_range_is_disjoint_from_every_other_producer`)
must refuse the crossing.

## Acceptance

- [ ] `next_quantifier_variable` never mints inside any other producer's
      band (refusal or disjoint rehash), with a regression asserting the
      boundary from both sides.
- [ ] `scripts/check.sh` green.
