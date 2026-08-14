# Resource contexts materialize and rescan pairwise relationships

`ResourceContext` operations must not enumerate unrelated resource pairs.
The original violations — quadratic validity checks, eager cross-family
separation pairs, linear exact consumption, restart-based normalization —
are fixed, indexed, and curve-gated. What remains is one investigation:
deleting the last eager pair emission (symbolic same-block memory
separations) breaks exactly one test, and the divergence point is narrowed
to independent contract certification's replay but not yet named.

## Current state

Start from the local branch `claude/lazy-separation-prototype-rebased`
(commits `f460c729`, `851fde96`, `66064886`; rebase onto master first —
several agents commit daily). It deletes same-block pair emission and serves
`memory_separation_candidates` from an incrementally maintained index
projected from the compact `CResourceComposition` carriers — entries
identical to the former pair propositions, never materialized into ambient
proposition sets. This is the issue's required design ("materialize an
explicit proposition only when a certificate asks for it").

Under that prototype, the full default suite passes except one test:

```sh
cargo test --lib -- execute_until_expands_vector_storage_call_postconditions
```

Its `buffer_pipeline` proof partially executes, unfolds `buffer_storage`,
proves two `have`s, and folds `nonempty_buffer`. With pairs present,
independent certification's replay of that sequence produces an outcome
exactly equal to the desired one. Without pairs, the certified path's final
resources still hold `buffer_storage` folded plus a stray view where
`nonempty_buffer` should stand — the independent replay takes a different
course through the unfold/have/fold sequence itself.

## The one remaining question

Trace the independent certification replay's resource state step by step
against the planning replay's, on that one test, and find the first tactic
where they diverge without pairs. That step names the exact query the
compositions must serve; every consumer converted so far needed one bounded
composition fallback at one query site. Two are already converted and
verified on the prototype: post-store certificate transport
(`expanded_read_step_keeps_named_range_separation_premises`) and the
modular-call snapshot path
(`modular_call_snapshot_anchor_replays_with_owned_resource`).

## Measured and eliminated — do not re-walk

- Comparison-side fixes cannot work: with pairs the representation
  certifier never engages (outcomes exactly equal), and adding proof-aware
  composition fallbacks to both the pointer and range disjointness variants
  changed nothing for this test (the pointer one did convert the
  owned-string consumer and is landed; the range one is on the prototype).
- The memory-cell mismatch ("memory snapshots differ", materialized
  call-havoc cells, effect-summary endpoint matching) is downstream shadow
  of the resource divergence, not cause.
- Candidate multiplicity, bucket sizes, and prover fallthrough in the lazy
  index are all measured fine; an earlier lazy-rebuild variant of the index
  was too slow and the incremental maintenance replaced it.
- A budget exhaustion in `box_pipeline` was a separate pre-existing cost
  (certificate construction's ambient rewrite harvest), fixed on master;
  see `atomic-derivation-returns-premises-not-steps.md`.

## Remaining to close, in order

1. The trace above; give the diverging query its composition fallback.
2. A red deterministic curve: N symbolic same-block owned ranges through
   `observable_facts_assuming_valid` must emit no `CResourceSeparate`
   propositions and near-linear work (red on master today, green on the
   prototype).
3. Full gate on the merged prototype; the three frontier tests are the
   sensitive ones, but the fixture gates never ran to completion under the
   prototype.
4. Close-out per `README.md`: durable design into the efficiency guide's
   lazy-separation material, delete this file, and update the burndown —
   which then records zero demonstrated asymptotic violations.

## Landed and gated (for reference)

Exact/family/shape/block/endpoint indexes on `ResourceContext`; ordered
interval validation and insertion; concrete-range and distinct-block
separation without pairs; token/composite pairs removed via the compact
carrier; incremental memory-separation and loadability indexes on
`Assumptions`; indexed non-exact satisfaction and definitional consumption;
checked-execution rebasing at the contract boundary. Curves:
`unrelated_resource_normalization_has_linear_deterministic_work`,
`adjacent_memory_normalization_has_linearithmic_deterministic_work`,
`disjoint_concrete_range_validity_scales_near_linearly`, the
fixed-candidate lookup/consumption regressions, and
`compact_composition_projects_symbolic_separation_without_pair_facts`.
Rejected designs that must not return: a vector-backed loadability bucket
(changed smart-search order), exact-only core deduplication (left stale
views usable after frees), an opaque composition that hid evidence from
condition contradiction, and unrestricted recursive-resource equivalence
probes (measured at 9.5 seconds).
