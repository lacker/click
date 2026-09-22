# The owned-overlap rule misses cross-block pairs with proven equal bases

P1. Ownership is a partition of *addresses*; two owners over proven-equal
spellings of the same bytes are one double claim, not two disjoint members.

## What was found

`memory_ranges_proven_overlapping`
(`src/kernel/primitives/resource_algebra.rs:5559`) decides overlap for the
composition partition invariant (`MemoryResourceAlgebra::pair_validity_error`,
`resource_algebra.rs:4732`). Its cross-block route reduces the pair through
`element_index_from_base_with_width`, which answers `None` whenever the two
bases are spelled in **different blocks**, and the rule then answers "not
proven overlapping" — even where assumed pointer equalities prove the two
bases are one address. The code comment right above even cites the loan
oracle ("exactly as the loan oracle does,
`protected_range_proven_overlapping`"), but the loan oracle consults
`exact_pointer_aliases` and this rule does not.

Machine-confirmed: `hunt_investigation_owned_overlap_through_equal_spellings_is_not_proven`
(`src/kernel/primitives/resource_algebra.rs` investigation module) — two
owners over one range spelled on an `ExternalArgument`-based pointer and on
`Symbolic` spelling that `q == (the argument pointer)` proves equal are *not*
proven overlapping.

Composition accepts both owners (the pair sweep never pair-checks
cross-block pairs: `try_compose_into_valid_context_delaying_normalization`
buckets by `right_range.base().block`). The partition premise is later
spent by `proves_owned_memory_ranges_separate_shallow`
(`resource_algebra.rs:2334`) as separation evidence in
`owned_composition_store_separated_evidence`
(`src/kernel/memory_provenance.rs:1844`) and the store ladder
(`src/kernel/resource_tracker/step_effect.rs:383`): a store through one
spelling is "separated" from a load through the other, and the load survives
with its pre-store value — a false theorem over bytes the store wrote.

## Intended regression

The investigation test as a true regression:
`memory_ranges_proven_overlapping` must answer `true` for the
equal-spelling pair above, e.g. by rebasing cross-block pairs through the
same alias routes the loan oracle uses before deciding the byte overlap.
Then the composition acceptance refuses the double owner and the
separation law never sees an aliased pair as two members.

## Acceptance

- [ ] The deciding rule proves the aliased pair overlapping (or the
      composition insertion refuses the cross-spelling double owner), with
      the equal-spelling regression green.
- [ ] `scripts/check.sh` green.
