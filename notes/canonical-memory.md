# Canonical memory: decisions and state

*Working note (see `notes/README.md`). Full session-by-session history is
in git log for this file; this is the living summary.*

## Decisions locked with the repo owner

- **A then C, skip B**: interning first (landed), named memory states as
  the eventual rewrite, no construction-time canonicalization.
- Thread-local arena, unbounded growth accepted (flag in item-10 debt).
- `Eq`/`Hash` by arena ID + content hash; `Ord` keeps a same-ID fast path
  then falls back to structural comparison (raw-ID ordering would make
  BTreeMap iteration nondeterministic — proof search is fuel-sensitive).
- Globally memoize only assumption-free work, keyed by interned identity.
- Field resources cover their full layout slot including trailing padding.
- **Everything the certifier consumes gets a surface spelling** (option b
  for effect-backed postconditions).

## What landed (step A and its follow-ons, 2026-07-29..30)

- `SharedCMemory` interning in `MemoryLoad` terms; memoized
  `canonical_memory_for_pointer_load`, `canonicalize_atomic_loads`,
  `canonical_c_memory_deep`. Lib suite ~2x faster.
- Endpoint/base load bridging in `memory_range_covers` /
  `split_memory_range` via `c_memory_load_is_unchanged` (reentrancy
  guarded).
- If-condition canonicalization inside `canonicalize_atomic_loads`
  (depth-propagated), canonical/resolution equality arms in `proves` and
  the atomic prover (depth-gated at 64), surface-spelling synthesis for
  effect-backed postcondition premises, loadability-from-load-facts rules,
  advance entry-spelled loadability export, theorem facts as certification
  assumptions with predicate instantiation.
- Net effect: master went from 14 visible mdtest failures to green
  (with 6 quarantined; see plan.md section 2).

## Why per-site bridging is over

The last two tests (vector_fill, field_derived) are quarantined as the
representation's residue. Evidence of exhaustion: the back-edge
bound-extension rule (`∀v<b` + final index ⇒ `∀v<b+1`, parked on branch
`claude/forall-extension-wip` with probes) passes every gate except the
final-index conclusion, whose proof needs an offset-premise match that
itself drifts by snapshot spelling; making that match resolution-aware
blew a 300 s budget. Each bridge begets another bridge. Three separate
stack overflows during this work all traced to structural recursion on
deep snapshot terms.

## The target structure (option C — the next big arc, not short-term)

A memory state is a name, not a value. States form a DAG: `m0` (entry),
`store(m, ptr, val)`, `havoc(m, region)`, `call(m, summary)`. Loads are
`load(m, ptr)`; equality across states is select-over-store algebra plus
write-disjointness from effect facts — what `certified_store_equations`
and the effect-chain BFS approximate today, but as the representation
instead of a patch layer. `old(...)` references a named earlier state.
Most comparison-time bridging machinery gets deleted rather than
extended. Migration risk concentrates in eval.rs store paths, resource
lowering, and every `CMemory` embedded in `Proposition`/`Term` variants.

Expected to clear: both residue mdtests, most of the quarantine backlog,
and the giant-term perf class (field_derived's ~500 s grouped-simp grind).

## Traps for whoever continues

- SOUNDNESS: never drop havoc/call-havoc blocks from canonical load
  memories (`memory_load_equality_does_not_ignore_loop_havoc_identity`
  guards this). Havoc blocks are semantic freshness markers.
- Guard and depth-gate every new recursive prover arm; the 64 MB child
  stacks in the harnesses are a backstop, not a license.
- Generation-side certificate self-checks must mirror the tactic-replay
  check exactly; recorded lowerings in `SurfacePropositionMap` round-trip
  where re-lowering drifts.
- `ConditionIs` facts live in `condition_facts`, not `prop_facts` — scan
  `pure_facts()` when both matter.
