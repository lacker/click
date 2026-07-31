# Expansion loses the aggregate `object(owner)` spelling

Status: open (small)
Claimed:

The last remaining lib `#[ignore]`:
`expansion_preserves_unfolded_resource_and_predicate_fact_spellings`
(src/lang/click/expansion.rs). `unfold` decomposes the aggregate
`object(owner)` separation into per-field facts, and the aggregate
spelling never reaches the emitted `step using` premises, so the assert
for the one-line aggregate form fails.

`object(owner)` is a documented canonical struct spelling
(conventions.md), so this is a genuine spelling regression — but it is a
printing/re-folding concern, not soundness. Note when fixing: the test's
`terminated_at` assert currently passes only incidentally (it matches the
resource *declaration* echoed in the expansion, not the step-using
block), so it is not really testing what it reads as.

Repro:

```
cargo nextest run --lib --run-ignored ignored-only \
  -E 'test(expansion_preserves_unfolded_resource_and_predicate_fact_spellings)'
```

Done when: the test passes un-ignored.
