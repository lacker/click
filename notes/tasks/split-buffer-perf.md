# split-buffer perf: last two SLOW audit findings

Status: done — `click-audit --keep-going examples` reports 0 site failures
Claimed: (clear)

Scope was: get the full `click-audit --keep-going examples` run to zero
SLOW findings by cutting owned_split_buffer_pipeline's unit verification.

## Result

`click-audit --keep-going examples`: **100 sites passed; 0 site
failures**; 175 s wall clock (was 314 s). The 2 remaining session
failures (owned-string, owned-vector) are the separate
store-provenance-family task.

The two SLOW sites are now comfortably inside the 10 s limit:
- `owned_split_buffer.click:235:5` — 18.3 s -> 5.5 s
  (expand 262 ms, verify 1703 ms, reverify 3490 ms, reexpand 22 ms)
- `owned_split_buffer.click:427:5` — 13.5 s -> 4.1 s

Targeted unit verify
(`click-verify examples/owned-split-buffer/owned_split_buffer.click:200:5`):

| phase                                  | before  | after   |
|----------------------------------------|---------|---------|
| `function owned_split_buffer_pipeline` | 9.10 s  | ~2.0 s  |
| contract execution                     | 3.63 s  | ~0.75 s |
| contract claims                        | 0.79 s  | ~0.25 s |
| whole-file verify                      | 11.1 s  | 3.06 s  |

`cargo test --test examples`: 11 s -> 3.57 s.

"Before" is master 56eb714 (i.e. after the pipeline's final
`execute_rest` was expanded, which had already removed an 8.6 s tactic;
pre-expansion the unit was 16.9 s).

Gates after both commits, rebased onto master f91bb5f:
`cargo nextest run --lib` 468 passed; `cargo test --test mdtests` ok;
`cargo test --test examples` ok (3.84 s).

## Root cause

Both fixes are in the same hot path. The composite-resource expansion run
at every verified call
(`expand_all_composite_resource_facts` -> `ResourceContext::normalized`
-> `memory_range_covers` -> `range_covered_by_fact_range` ->
`pointer_element_index_from_base`) asks a handful of range-bound
comparisons per resource-fact pair. ~700 resource-pair normalizations
fanned out into 140 k `decide` calls, 2.9 M `condition_matches` and
940 k memory-load equality searches — 77 % of the whole profile. The
contract execution was not intrinsically expensive; it was paying for
two avoidable amplifiers underneath.

**1. Constant lookup proved equalities it could not use** (commit
"Test the constant side before the equality search in constant lookup").
`Assumptions::signed_constant_known_equal` swept every condition fact in
the expensive order:

```
if self.bitvector_terms_proven_equal(term, left)          // deep search
    && let Some(value) = signed_bitvector_constant(right) // syntactic fold
```

For every fact whose other side is not a constant — nearly all of them —
the memory-load-bridging search was pure waste. It sits under
`decide_signed_comparison_from_equal_constants`, which every signed
comparison in `decide_from_order_facts` consults, so it was 56 % of the
profile on its own. Fix: hoist the two `signed_bitvector_constant` tests
above the equality searches they already gated. This is a short-circuit
reorder of a conjunction of two pure predicates over a deterministic
`BTreeMap` walk, so the same constant comes back for the same fact sets;
no check was weakened, because a fact with no constant side could never
have answered the query. 9.10 s -> 2.71 s.

Same shape as the earlier owned-segmented-buffer win. The earlier fix
added the `plausibly_equal` gate to the *sibling* walk
`signed_constant_after_equality_normalization_inner`;
`signed_constant_known_equal` had been left ungated.

**2. Fact-transport equality was recomputed instead of cached** (commit
"Memoize fact-transport equality by fact-set content identity").
`has_condition_fact` asks `bitvector_terms_equal_for_transport` for every
candidate fact of every decision, and `condition_matches` asks it up to
four more times per candidate. The same term pairs recur constantly, but
the search was uncached. Fix: memoize it with `decide`'s discipline — a
`true` is evidence found in the facts and is always cacheable; a `false`
computed under an ambient truncation (memory-resolution fuel, the
memory-load depth guard) is path-dependent and is not cached; the key
carries the fact set's content identity, and the memo is only consulted
under an enclosing `AssumptionsIdScope` so no call pays a fact-set hash.
`CLICK_DISABLE_DECIDE_MEMO` bypasses it. 2.71 s -> ~2.0 s.

## Method

- `sample <pid> 18 -f out.txt` against a running `click-verify`, then
  aggregate inclusive samples per frame. That is what located both
  amplifiers.
- Temporary `CLICK_PROBE`-gated atomic counters in
  `assumptions.rs`/`primitives.rs` gave the fan-out ratios
  (~700 `normalize_pair` -> 140 k `decide` -> 3.6 M fact scans). All
  probes stripped before committing.

## Dead ends (reverted, do not retry as-is)

- **Negative-pair memo in `ResourceContext::normalized`.** Every merge
  restarts the O(n^2) sweep, so rejected pairs are re-proved once per
  merge; caching the rejects by content is exactly equivalent (the pair
  function is pure in its two facts and the fixed assumptions). Measured
  *slower*: 2.71 s -> 3.14 s. Duplication is low and cloning
  `CResourceFact` keys costs more than the re-proof it avoids.
- **Lazy `end_is_covered` in `range_covered_by_fact_range`.** The
  end-coverage decision is computed eagerly before the lower-bound
  decision it is ANDed with; making it lazy is a free equivalent
  reorder. No measurable change — that first block rarely fires.
- **Considered and rejected on soundness grounds:** hoisting the
  positive arms of `pointers_proven_equal_for_memory_resolution_with_depth`
  above its `pointers_proven_disjoint_by_explicit_range_...` guard.
  That guard is 81 % of the function's cost and is skippable whenever
  the positive part fails, but reordering makes the guard more likely
  to lose its fuel race, i.e. it weakens a soundness check for speed.
  A safe version exists (return `false` early only when the positive
  part is *structurally* impossible, which gives the identical answer)
  but was not needed once the audit had headroom.
- Not done: adding the `plausibly_equal` structural gate to
  `signed_constant_known_equal` as well. It is a real
  (completeness-affecting) prefilter, and after fix 1 that function is
  no longer hot. Left as a lever if this unit regresses.

## Remaining profile, if this ever needs more

After both fixes, ~60 % of the unit is still
`range_covered_by_fact_range` -> `pointer_element_index_from_base` ->
`decide(PointerOffsetEqual)` -> memory-resolution pointer equality. The
next real win there is structural, not a reorder: either fewer
`expand_all_composite_resource_facts` calls per verified call, or
memoizing `pointer_element_index_from_base` under the same
truncation discipline.

Repro:
  CLICK_TIMINGS=1 ./target/debug/click-verify \
    examples/owned-split-buffer/owned_split_buffer.click:200:5
  ./target/debug/click-audit --keep-going examples
