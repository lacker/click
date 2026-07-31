# split-buffer perf: last two SLOW audit findings

Status: fixed (pending audit confirmation line below)
Claimed: worktree-agent-aa455ca39fbbaf91c 2026-07-30

Scope: get the full `click-audit --keep-going examples` run to zero
SLOW findings by cutting owned_split_buffer_pipeline's unit
verification.

## Root cause

`Assumptions::signed_constant_known_equal` swept every condition fact
looking for one that names a constant for the queried term, and it ran
the conjunction in the expensive order:

```
if self.bitvector_terms_proven_equal(term, left)
    && let Some(value) = signed_bitvector_constant(right)
```

`bitvector_terms_proven_equal` is the memory-load-bridging equality
search (it recurses through `memory_loads_proven_equal`, pointer
resolution and nested `decide`); `signed_bitvector_constant` is a
syntactic constant fold. So for every fact whose other side is *not* a
constant — the overwhelming majority — the sweep paid a full bridging
search whose answer could not be used.

`signed_constant_known_equal` sits under
`decide_signed_comparison_from_equal_constants`, which every signed
comparison in `decide_from_order_facts` consults. The composite-resource
expansion done at each verified call
(`expand_all_composite_resource_facts` -> `ResourceContext::normalized`
-> `memory_range_covers` -> `range_covered_by_fact_range` ->
`pointer_element_index_from_base`) asks a handful of range-bound
comparisons per pair, so ~700 resource-pair normalizations fanned out
to 140 k `decide` calls, 2.9 M `condition_matches` and 940 k
memory-load equality searches. That single sweep was 56 % of the whole
process profile.

Same shape as the earlier owned-segmented-buffer win: a search running
snapshot-bridged equality against every candidate fact. The earlier fix
added the `plausibly_equal` gate to the *sibling* walk
`signed_constant_after_equality_normalization_inner`;
`signed_constant_known_equal` was left ungated.

## Fix

Hoist the two `signed_bitvector_constant` tests above the equality
searches they already gated (src/kernel/assumptions.rs). This is a pure
short-circuit reorder of a conjunction of two pure predicates over a
deterministic `BTreeMap` iteration, so it returns exactly the same
constant for exactly the same fact sets — no check was weakened, no
candidate that could have answered was discarded. The only observable
difference is that unusable equality searches no longer burn simp
reasoning fuel, which can only let later searches see more, never less.

## Numbers (debug build, this machine, 2026-07-30)

Targeted unit verify
`click-verify examples/owned-split-buffer/owned_split_buffer.click:200:5`:

| phase                          | before  | after   |
|--------------------------------|---------|---------|
| `function owned_split_buffer_pipeline` | 9.098 s | 2.708 s |
| contract execution             | 3.626 s | 1.045 s |
| claim paths prepared           | 0.749 s | 0.221 s |
| contract claims                | 0.785 s | 0.258 s |
| whole-file wall clock          | 11.1 s  | 4.4 s   |

`cargo test --test examples`: 11 s -> 4.79 s.
(Both "before" columns are measured after master's 56eb714 expansion of
the pipeline's final `execute_rest`, which had already removed an 8.6 s
tactic; pre-expansion the unit was 16.9 s.)

Gates: `cargo nextest run --lib` 465 passed; `cargo test --test mdtests`
ok; `cargo test --test examples` ok.

## Method / dead ends

- Profiled with `sample <pid> 18 -f out.txt` on a running `click-verify`
  and aggregated inclusive time per frame. 76 % of the process sat under
  `range_covered_by_fact_range` -> `pointer_element_index_from_base`,
  and 56 % under `signed_constant_known_equal`.
- Temporary `CLICK_PROBE`-gated atomic counters in
  `assumptions.rs`/`primitives.rs` gave the fan-out ratios above
  (~700 `normalize_pair` -> 140 k `decide` -> 3.6 M fact scans). All
  probes stripped before committing.
- Not a dead end but worth recording: the task file's "3.6 s contract
  execution is the lever" framing was right about *where* but not about
  *why*. The contract execution is not intrinsically expensive; it was
  paying for one badly-ordered conjunction, and the same conjunction was
  also charging the claims phase and the ordered-replay verification.
- Deliberately not done: adding the `plausibly_equal` structural gate to
  `signed_constant_known_equal` as well. It would prune further but it
  is a real (completeness-affecting) prefilter, and the free reorder
  already gave 3.4x. Left as a lever if this unit ever regresses.

Repro:
  CLICK_TIMINGS=1 ./target/debug/click-verify \
    examples/owned-split-buffer/owned_split_buffer.click:200:5
  ./target/debug/click-audit --keep-going examples
