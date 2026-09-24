# `click expand` emits a rewrite that exceeds the checked nesting limit

## Violated invariant

`click expand` must either produce a rewrite that verifies or refuse with an
actionable diagnostic. It must never write a proof the verifier then rejects
(`AGENTS.md`, "Tooling stability comes first").

Today the expander happily emits an explicit proof whose regions nest twelve
deep, and only the reverification of that rewrite fails with "this proof nests
12 execution regions; the checked proof drivers support at most 11". The
expansion step itself reports success.

## Reproduction

Take the frozen round trip in `mdtests/byte_representation_roundtrip.md` (four
null-checked allocations, each failure path freeing the earlier ones) and add
eight more null-checked `malloc` calls of the same shape before the copies,
so the expanded proof nests twelve proof `if`s. Verify with
`execute(); simp();`, which passes, then
`click expand --claim f.contract`. The rewrite is written, and verifying it
fails with the nesting diagnostic. Seven extra allocations (eleven regions)
expand and reverify. The generator
`roundtrip_with_unrelated_allocations(8, 0)` in
`src/surface/tests/scaling_tests.rs` produces the failing source.

## Intended regression

An expansion whose explicit rewrite would exceed
`MAX_CHECKED_PROOF_REGION_NESTING` is refused before anything is written, with
the same nesting diagnostic the verifier gives and a pointer to the usual
remedies (move an inner region into a contracted helper, or prove part of it
in a `have`). A fixture pins that twelve nested null checks are refused by
`expand` with that message and that eleven still expand and reverify.

## Acceptance criteria

- `click expand` never reports success for a rewrite that fails
  reverification because of the region nesting bound; the refusal names the
  bound and the remedies.
- The existing `mdtests/nested_null_check_chain_expands.md` and
  `mdtests/sequential_returning_branches_nesting_bound_named.md` keep passing.
- `click audit` and `click expand` agree on the refused case.
- `scripts/check.sh` passes. Delete this issue and its list entry when the
  refusal, its regression, and any documentation land.

Whether the nesting bound itself should be raised, or continuations of a
returning arm should stop counting as a level, is a separate design question
and is not required here.
