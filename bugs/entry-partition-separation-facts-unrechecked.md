# Entry-partition separation facts are never re-checked after equalities

P1. A separation fact and a later-proven equality over the same bases are
jointly inconsistent; the proof layer must refuse, not serve the stale
separation.

## What was found

`contract_entry_partition_facts` (`src/kernel/functions.rs:17178`) installs
`Proposition::CResourceSeparate` between owned and viewed clause bases whose
entry-time relation is undecided merely because a whole-clause/configuration
was not falsified ("no decision" at that point Lindqvist mode / "proven
distinct"?). The only filter at install time is
`owned.base().blocks_proven_distinct(viewed.base())` (functions.rs:17196) —
i.e., the fact asserts the address-level claim from clause *spellings*,
sound only as long as no later context fact can prove the bases equal.
Nothing re-checks:

- the hop consumer is presence-only:
  `src/kernel/resource_tracker/cell_source.rs:271-281` accepts the fact when
  `assumptions.prop_facts.contains(proposition)` and the operands match
  structurally, plus the callee composition member evidence
  (`managed_memory...`); it never consults whether the bases are now
  proven-equal in the current context;
- the containment candidate scan
  (`src/kernel/memory_provenance.rs:1746-1808`,
  `typed_store_separated_ranges_evidence`) likewise serves a present
  separation over the two blocks regardless of newly established
  equalities;
- the call-side planner (`install_borrowed_contract_inputs`,
  `src/kernel/api.rs:2454-2488`) refuses only pairs *provably* overlapping
  at entry (under `assumptions_without_memory_separations`), so undecided
  pairs enter with separation licenses and prove them false later
  (e.g. a nested call's `ensures result == a; ensures result == b;`, or a
  match-arm binding via `arm_binding_program_spelling`,
  `functions.rs:14415-14434`, which re-spells a bound pointer through its
  proven-equal alias).

The same absence of re-derivation widens through
`owned_composition_store_separated_evidence`
(`src/kernel/memory_provenance.rs:1852`): two owned members over disputed
aliasing spellings pass the pair_validity check (provably-overlapping only)
at insertion and the separation law is spent by *entry containment* at hop
time. With the alias-equal pair the store through one spelling is framed as
separate from the load through the other, and the load answers its
pre-store value over bytes the store wrote — the false-theorem direction
over the same bytes.

The re-derivation must happen at every hop `checks` time (when the fact is
*used*, not when it was *assumed*), i.e. wherever
`proposition prop_facts presence` is trusted.

## Intended regression

A proof-level regression: an entry pair `owns a[0..1]; views b[0..1];` whose
aliasing relation is undecided at entry, plus a body-level fact proving
`a == b` (nested-call ensure or match binding), must NOT have its store
through `a` framed separated from a load through `b` via the entry
separation fact; the framed load must report affected and (upon the join)
a diagnostic or a false separation refusal.

## Acceptance

- [ ] Every `CResourceSeparate` presence-based hop re-derives its operands'
      distinctness against the current context's equalities (or the
      assumption layer invalidates a separation provable-inconsistent with
      new equality facts), with the post-entry-equality regression refusing.
- [ ] `scripts/check.sh` green.
