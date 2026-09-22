# spec-fold binder identities overlap the surface quantifier binder bands

P1. Fresh identifiers must come from a range owned by their producer. A
binder that equals a free identity of another producer is exactly the
capture that binder-elimination rewrites cannot see.

## Invariant

`spec_fold_bound_variable` (`src/kernel/spec.rs:7070`) mints fold binders as
`Variable(3_000_000 + (hash(name) % 1_000_000_000))` — the band
`[3_000_000, 1_003_000_000)`, derived purely from the user's accumulator and
item names. The surface annotation lowerers mint quantifier binders from
bases inside that same band: `3_000_000` (`src/surface/lowering/annotations.rs:843`),
`3_100_000`, `3_200_000`, `3_300_000` (lines 492, 578, 659, 1419, 1485), and
the algebraic-binder producer steps `4_000_000` by `65_536` (lines
4767-4778). Every other identifier producer owns a disjoint band and a
disjointness test (`the_match_binder_range_is_disjoint_from_every_other_producer`,
`the_universal_witness_range_is_disjoint_from_every_other_producer` in
`src/kernel/primitives/derivations.rs`); this producer has neither. The
kernel execution counter deliberately refuses below this band
(`src/kernel/primitives/derivations.rs:1113`) but the quantifier and
algebraic-binder lowerers do not.

Because a fold's two binders come from the *same* string, an accumulator
named like any existing binder identity can capture a surface quantifier's
bound variable in one direction, or the reverse in the checking direction:
facts spelled under two different written binder names at one identity can
be joined into one scope. The false-theorem direction is a proof whose goal
requires distinguishing the two binders.

## Intended regression

A test asserting disjointness between all minting producers with the same
shape as the match-binder and witness disjointness tests: the fold band
`spec_fold_bound_variable` can produce (enumerate the salt pair and a set of
realistic names) must not intersect the quantifier bases 3_000_000,
3_100_000, 3_200_000, 3_300_000 used by `AnnotationLowerer`, nor the
algebraic binder band, nor any producer asserted there.

## Acceptance

- [ ] Either the fold band is carved into its own disjoint universe (with the
      disagreeing producers refusing or rehashing on collision), or every
      colliding producer is moved out of the band, with a disjointness test
      guarding the boundary from both sides.
- [ ] `scripts/check.sh` green.
