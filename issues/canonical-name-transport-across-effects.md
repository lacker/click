# Canonical load names do not connect across effects in explicit transports

> STATUS (2026-08-19): the connect mechanism LANDED on master at 7c9f6553
> and both reproductions verify under a green `scripts/check.sh`. What
> keeps this file open is the second acceptance criterion: there is no
> deterministic regression that fails if a general load-alias search
> re-enters the transport path. The bounds themselves are in place
> (`with_isolated_memory_resolution_fuel`, `with_bounded_snapshot_comparison`,
> the frame-only composite channel) and documented at their sites; they are
> simply not pinned by a test.

## Violated invariant

An explicit `transport(at(P, e) == X, e == X) using { ... }` with correct
premises must connect a recorded-point spelling of a load to its
current-point spelling whenever the intervening effects provably leave the
cell unchanged, and it must do so in work bounded by the tactic's explicit
input — never by re-deciding load-term aliasing recursively.

With content-addressed canonical load naming (the
`claude/load-canonicalization-wip` branch), the two spellings are distinct
canonical variables whenever a call havoc or an undecided-alias store
separates their snapshots, and no consumer can currently connect them:

- `examples/input-cursor` fails at
  `input_cursor_shared_pipeline.contract` have proof 10: the explicit
  transport's target names the current point (`v1810…`), and the fact set
  holds only earlier names (`v1406…`, `v1840…`), separated by call havocs
  whose preservation is effect-summary evidence, not DAG structure.
- `mdtests/field_derived_precise_effect_after_metadata_write.md` fails the
  same way at `buffer_push.contract` have proof 6; the separating store
  writes `data[len]` with a symbolic index, so the cell-preservation
  question is exactly the load-vs-load aliasing recursion the naming
  migration exists to avoid.

## What has been established (see WIP-FALLOUT.md on the branch)

- The registry keeps both the canonical (jumped) spelling and the
  first-seen origin snapshot per name; transports and resolvers use
  origins, which are live and DAG-connected.
- Epoch keying at mint cannot unify these names: the memory DAG records no
  call-havoc edge kind, so the walk correctly stops at calls, and the
  metadata-write store's alias question is undecidable cheaply at mint.
  The names SHOULD differ; the connection is evidence-based.
- Free search over registry-resolved load spellings inside the transport's
  reachability walk burns the tactic's whole 2M-unit budget
  (metadata-write) — it reconstructs the recursion canonicalization
  removed. An isolated 8k-node fuel bound on that retry cut the cost but
  broke `restricted_simp_certifies_unchanged_prefix_after_indexed_store`,
  whose legitimate connection needs more than the bound allowed; the
  bound was reverted.
- Hop-by-hop respelling at statement introductions
  (`transport_framed_atomic_bitvector`'s canonical-variable arm plus the
  widened `c_condition_fact_has_memory` gate) works where
  `memories_match_for_pointer_load` or the directly-unchanged check
  accepts the hop, and fails where only composed effect summaries prove
  preservation: `c_memory_load_is_unchanged`'s effect arms demand exact
  memory identity per hop and do not compose across several effects.

## Design question to decide

Where should the connection live?

1. **Introduction-time respelling made complete**: make the per-statement
   respelling accept every hop the effect evidence supports (compose the
   effect-fact arms, accept origin handles for `effect_before`/
   `effect_after` up to interning), so the current-point name is always
   available and explicit transports connect syntactically. Cost is paid
   once per statement per fact, at introduction; the transport tactic
   stays search-free. This matches how load spellings behaved before the
   migration and is the leading candidate.
2. **A dedicated bounded connect inside the transport tactic**: chain
   single-hop origin-unchanged edges (each hop one effect fact, decided by
   range disjointness against the explicit premises) rather than a general
   reachability walk. Bounded by (hops × premises); no general search.
3. Both, with (1) primary and (2) as the fallback for facts that were
   never introduced (spelled fresh inside the have body).

## Intended regression

- `examples/input-cursor` verifies inside its 30s limit.
- `mdtests/field_derived_precise_effect_after_metadata_write.md` passes
  with the `owner->data` have deciding in the same order of magnitude as
  its `owner->cap` sibling (the original motivating budget), not by
  raising any budget.
- `restricted_simp_certifies_unchanged_prefix_after_indexed_store` and the
  full lib suite stay green.

## Acceptance criteria

- Both reproductions above green under `scripts/check.sh` with no budget,
  limit, or example change.
- The connect mechanism's work is bounded by explicit tactic input and
  effect-hop count, documented in the code, and exercised by a
  deterministic regression that fails if a general load-alias search
  re-enters the transport path.
- This file and its Open-list line are deleted when the fix lands.
