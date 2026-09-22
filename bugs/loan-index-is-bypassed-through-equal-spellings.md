# The indexed loan route is bypassed through a proven-equal spelling

P1. A loan protects the bytes an address designates, not one spelling of it.

## What was found

`permits_memory_access_with_assumptions` (`src/kernel/loans.rs:3785`) has two
routes. The unindexed route consults
`protected_range_proven_overlapping`, which rebase both sides through exact
pointer alias facts. The **indexed** route (line 3793) walks the dyadic
index whose buckets are keyed by `(block, level, start)` of the recording
spelling — `memory_interval_nodes`
(`src/kernel/primitives/resource_algebra.rs:126`) keys nodes on the query's
own block — and never consults assumed pointer equalities. A concrete query
spelled through an alias of the loan's protected range finds empty index
buckets, is never in `unindexed_memory` (indexed loans are filtered out of
it), and is **permitted** with `Ok(())`.

Machine-confirmed on the `claude/soundness-hunt-phase2b` branch:
`hunt_investigation_indexed_loan_is_bypassed_through_an_equal_spelling`
(`src/kernel/loans.rs` investigation module) lends a concrete loan over
`global:g[0..16]`, assumes `q == g`, and the write query over
`global:q[0..16]` is permitted while the same query over `global:g` is
refused.

Unsound-accept call sites riding on it: `validate_branch_memory_delta_against_loans`
(`src/kernel/api.rs:1182`, consult with an empty context), the decisive
"new local authority cannot bypass an existing loan" gate (`loans.rs:2632`
area), and `refuse_retiring_a_lent_allocation`
(`src/kernel/functions.rs`, the ledger scan that is the only guard after the
owner has left the residual).

Additional caller found by a later audit pass: the unindexed fallback's
`unindexed_memory.get(&range.base().block)` (`src/kernel/loans.rs:3807`) is
an exact-block map with no alias consultation, and the free/realloc consult
wrapper `stable_loan_memory_range_outcome` (called from
`src/kernel/eval/statements.rs:1868` for free and `:1496` for realloc)
reaches it with path facts only. A loan recorded under one spelling and a
free through a proven-equal spelling misses it: the free proceeds without
the loan refusal, and the stale-resource scan that follows inspects facts,
not ledger entries. Include this caller in the fix; one deciding route,
two consumers.

## Intended regression

The investigation test as a true regression: after applying a loan whose
memory backing is concrete, a permits query whose range's base block differs
from the recording spelling only through an assumed pointer equality must be
*refused* with `ActiveDependency`. The repair must make the indexed route
consult the same alias machinery (`exact_pointer_aliases`/exact pointer
equality) before it treats empty buckets as a permit; if consulting aliases
at the index key is impossible, the cross-spelling route must fall back to
the alias-aware unindexed comparator.

## Acceptance

- [ ] `permits_memory_access_with_assumptions` refuses the aliased write
      through the loan alias, with the equal-spelling regression passing.
- [ ] `scripts/check.sh` green.
