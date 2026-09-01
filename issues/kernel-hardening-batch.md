# Close five latent kernel asymmetries

Found by the 2026-09-01 kernel audit at cb034b21. Each item below is a real
code defect that an adversarial trace found unreachable from C source or proof
scripts today. They are grouped because each is a small, self-contained fix
with its own test; split this file if any of them grows.

1. **Interior heap pointers classified function-fresh.**
   `is_function_fresh_heap_pointer`
   (`src/kernel/api/contract_certification/contract_claims.rs:1274-1291`)
   tests `!matches_allocation(entry_memory) && matches!(block, Heap(_))`,
   and `matches_allocation` compares whole pointers, so `Heap(id) + 8` into a
   block live at entry is treated as fresh and skips the mutable-range check.
   Unreachable because ownership gates every store, but the classification
   should be block-identity based like `CMemory::is_live_heap_address`
   (`src/kernel/primitives/memory_state.rs:275`).
   Test: an effect claim for a function storing through an interior pointer
   into an entry-live block outside its declared footprint must fail.
2. **Free-variable collection misses symbolic block sizes.**
   `collect_memory_bitvector_variables`
   (`src/kernel/reasoning/variable_collection.rs:948-961`) visits block keys
   and cells but not `CBlock.size`, while
   `substitute_bitvector_variable_in_memory`
   (`src/kernel/reasoning/substitution.rs:1784-1799`) does rewrite sizes. A
   variable free only in a block size is invisible to
   `without_free_bitvector_variable` and to the capture-avoiding reserved set.
   Test: a memory with a symbolic block size `n` reports `n` as free.
3. **Interface joins accept uncertified effect facts.**
   `src/kernel/proof/execution.rs:1156` and `:1177` accept
   `CMemoryMutatesOnly` and `CMemoryEffectSummary` arm facts without
   `is_certified()` and without checking the declared ranges cover the
   before-to-after diff, unlike the catch-all at `:1203`. Unreachable because
   `ExecutionProofCore.effect_facts` is `pub(crate)`. The asymmetry is
   unexplained; require certification or document why it is safe.
   Test: an uncertified `CMemoryMutatesOnly` arm fact is rejected at the join.
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
   This is the mechanism behind [have-binder-capture.md](have-binder-capture.md)
   and [legacy-pure-theorem-checker.md](legacy-pure-theorem-checker.md).
   Resolve by making every publication go through a checked operation that
   derives the fact, or by narrowing the callers to the kernel and documenting
   the remaining trust. Coordinate with [double-execution.md](double-execution.md),
   which removes the re-execution that currently masks this.

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
