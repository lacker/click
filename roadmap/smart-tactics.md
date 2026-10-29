# Smart tactics: fast checking and enforceable search boundaries

Priority: P1.

Soundness: not soundness. This item concerns checking cost and separation of
search from checking. No false acceptance is known. Proof repairs must preserve
the original C and claims; preserving all automatic proof coverage is not a
requirement.

## Scope

Track remaining work only. The contract is in
[Verifier design](../docs/internals/verifier-design.md),
[Verification efficiency](../docs/internals/verification-efficiency.md), and
[Smart and simple tactics](../docs/concepts/smart-and-simple-tactics.md).

Fast checking must scale with explicit input, indexed access and the state
delta. Expansion cannot remove its cost. The implicit closer is separate from
`step()` checking: budgeted, expandable premise selection in `solve` or the
closer is legitimate search, even when a bare step invokes that closer.

Arithmetic premise collectors such as `signed_constant_bound_facts` are not
fast-checking defects merely because they enumerate candidates. Their current
ambient callers select proofs in the smart closer/planner; checking a written
certificate may traverse its explicitly cited premises. Add a collector to the
work below only with a demonstrated checking caller or an expansion/budget defect.

## Remaining checking walks

These are concrete checking call paths. Code inspection establishes the walks;
measure their growth before choosing fixes. Existing flat tests with unrelated
facts do not establish flat cost as the queried class or bucket grows.

1. **Compact-run store preservation.**
   `run_slots_kept_by_store` still asks
   `typed_ranges_disjoint_from_pointer_evidence` and may inspect symbolic slots.
   Complete the conservative-forgetting experiment, retaining deterministic
   growth tests for logical run sizes and separation/ownership buckets.
   Repair affected proofs with explicit separation and transport while
   preserving C and contracts. Validate the remaining descriptor/range proofs
   and expansion before landing compact-run changes.
   Keep actual changed-cell work separate from candidate discovery; add
   bounded automation only for demonstrated proof friction.
2. **Direct resource support selection.**
   `directly_supporting_owned_entry_with_separation` and
   `has_other_directly_supporting_owned_entry` in
   `src/kernel/primitives/resource_algebra.rs` examine candidate resources.
   Execution, call-resource checking and loan handling reach these helpers.
   Audit both memory and non-memory candidates; distinguish an explicitly
   selected resource or footprint from an implicit candidate bucket.
   Measure ambiguous buckets and refusals as well as exact hits.

Memory-history traversal and frame-query consolidation are tracked in
[Fact-aware frame walks](fact-aware-frame-walks.md). Coordinate overlapping
fixes there; this item does not duplicate that work or require a general audit
of all history upkeep, diagnostics, or verifier code before closure.

## Acceptance for each target

- Establish deterministic work curves at several sizes through a fast-checking
  caller. Charge candidate visits, include repeated queries and misses, and
  separate explicit input/state-delta growth from ambient candidate growth.
- Replace implicit enumeration with indexed summaries/selection, or decline
  with an obligation that explicit proof steps can discharge. Search for an
  alternative belongs in budgeted planning with an expandable explicit form.
- Retain semantic controls for widths, snapshots, aliasing writes and branch
  isolation. Branches extend persistent contexts; do not withdraw facts to
  backtrack. Preserve C and claims in proof repairs.
- Add growth regressions and the relevant checking/search API boundary guard.
  When search is involved, verify expansion without re-entering that search.
- Attribute excessive checking to checking even inside `solve`; legitimate
  search exhaustion remains a search diagnostic. Extend `CheckingWorkScope`
  where a migrated checker needs coverage, using explicit input/output measures,
  and preserve the existing nested-budget and accounting regressions.
- Update the design guidance alongside the enforced boundary. Remove each
  target when resolved by measurement and a fix or justified classification.

These are acceptance criteria for the named targets, not an open-ended list of
new audits. Add another blocker only with a concrete checking call path or
reproduction. Close this item once its named targets are resolved and their
regressions and boundary checks land; do not accumulate a completion history.
