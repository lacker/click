# Close five latent kernel asymmetries

Found by the 2026-09-01 kernel audit at cb034b21. Each item below is a real
code defect that an adversarial trace found unreachable from C source or proof
scripts today. They are grouped because each is a small, self-contained fix
with its own test; split this file if any of them grows.

1. **Interior heap pointers classified function-fresh.** Resolved by making
   `is_function_fresh_heap_pointer` classify entry-live allocations by block
   identity and adding the requested contract-effect regression.
2. **Free-variable collection misses symbolic block sizes.** Resolved by
   visiting block sizes in both free-variable and binder-variable collection;
   the regression also checks the existing substitution path.
3. **Interface joins accept uncertified effect facts.** Resolved by requiring
   certification for pointer and range memory effects, checking endpoint
   coverage, and validating conservative erased-cell endpoints against the
   kernel's call-havoc producer. The regressions cover uncertified effects,
   uncovered writes, and arbitrary erased cells.
4. **Premise-free ghost-invariant theorems.** The two owned-resource
   ghost-invariant axioms (`src/kernel/api.rs:2701-2757`) mint a `Theorem`
   with no premises whose conclusion is justified partly by
   `assumptions.proves(&conclusion)`, so the theorem is not premise-free
   valid (for example `Theorem(0 <= k)` for symbolic `k`). The wired consumer
   confines it; the shape violates the rule that execution theorems retain
   every verification condition as an implication premise.
   Test: the minted theorem's proposition includes the assumptions it used
   as premises.
5. **Unvalidated fact publication.** `ProofFacts::with_fact`
   (`src/kernel/proof/facts.rs`) and `publish_checked_focused_result`
   (`src/kernel/proof/object.rs`) are `pub(crate)` and check nothing, so the
   surface's fact bookkeeping is soundness-critical for everything not
   re-proved at contract certification (loop-phase proofs, pure theorems,
   resource scopes). `docs/internals/proof-objects.md` says the kernel
   containers never accept presentation as evidence; the fact store does.
   This is another example of why semantic fact publication must remain
   behind a checked kernel boundary.
   Resolve by making every publication go through a checked operation that
   derives the fact, or by narrowing the callers to the kernel and documenting
   the remaining trust. Double execution was removed on 2026-09-02
   (`docs/internals/proof-objects.md`), so no re-execution masks this now.

## Violated invariant

Effect certification classifies freshness by block identity; free-variable
collection and substitution agree on what is free; branch joins accept only
certified effect evidence; every kernel theorem's proposition carries the
assumptions it depends on; the persistent fact store accepts facts only from
checked kernel operations.

## Intended regression

The four tests listed inline in items 1 through 4, in `src/kernel/tests/`,
plus for item 5 a test that publishing an underivable fact (for example
`1 == 2`) through the checked publication path is rejected, or, if the trust
is documented instead, a test pinning that every caller of
`ProofFacts::with_fact` and `publish_checked_focused_result` lives under
`src/kernel/`.

## Acceptance criteria

- Each item has its fix and test, or a documented decision in the code
  explaining why the current behavior is safe and a test that pins the
  assumption the decision relies on.
- `scripts/check.sh` passes.
