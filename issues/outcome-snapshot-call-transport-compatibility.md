# Retire outcome compatibility for snapshot and post-call transports

## Violated invariant

Passing outcome proofs that transport one selected fact across a call or
memory snapshot should retain the checked `TransportUsing` step on the outcome
`Proof`. They still enter `outcome simp compatibility construction`, meaning
ordinary verification asks the legacy certifier to reconstruct a surface
transport after the semantic path has already succeeded.

This leaf is deliberately narrower than general atomic derivation: its source
and target are already identifiable from snapshot/call provenance. The missing
work is to expose that indexed evidence to the outcome proof and retain the
accepted transport directly.

## Current reproductions

- `mdtests/execute_expands_certified_post_call_fact.md` (`restore_one`)
- `mdtests/separate_symbolic_unwritten_read.md` (`write_i_read_j.keeps_j`)

The 2026-08-19 census records compatibility construction but no legacy exit
planning for these passing fixtures.

## Intended regression

- Each fixture records the selected source/target pair and forbids ordinary
  compatibility construction.
- Deleting the retained source or a required effect/separation premise from
  the expanded certificate makes independent replay fail.
- A multi-size query grows unrelated snapshot facts and proves selection is
  bounded by the source's provenance/effect bucket rather than the ambient
  fact set.

## Acceptance criteria

- Both fixtures verify without either outcome fallback span.
- The selected transport is checked once during smart construction and is
  retained verbatim in the `Proof` certificate.
- No recorded historical lowering is accepted as a newly stated target.
- Expansion, audit, and `scripts/check.sh` pass.

