# Retire outcome compatibility after checked branch continuations

## Violated invariant

A checked branch join and its common continuation already form one retained
proof-object lineage. A later outcome `simp` must consume that descendant
directly; it must not reconstruct the final claim through the compatibility
certifier because the facts originated in different arms or behind a joined
continuation.

## Current reproductions

- `mdtests/proof_branch_continuation.md` (`joined_increment.ensures_1`)
- `mdtests/proof_branch_interface_continuation.md`
  (`advance_nested_join.ensures_0`)

Both pass and avoid legacy exit planning, but the 2026-08-19 census records
compatibility construction for their final claims.

## Intended regression

- The checked split, both arm certificates, join, common continuation, and
  outcome closer remain one ancestry-checked `Proof` DAG.
- Failed outcome candidates discard their descendants and publish no partial
  expansion.
- A 16-through-4096 unrelated-fact curve retains the existing logarithmic
  branch/join allocation bound through final outcome closure.

## Acceptance criteria

- Both fixtures emit neither outcome fallback span.
- Certificate extraction traverses retained branch/outcome nodes only; it
  performs no premise discovery, semantic replay, or compatibility lowering.
- Expansion preserves deterministic arm and continuation order and
  independently verifies.
- `scripts/check.sh` passes.

