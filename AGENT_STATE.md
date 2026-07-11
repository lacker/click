# Agent State

Last updated: 2026-07-11.

This is a short handoff note for open work only. Canonical documentation lives
in `docs/`; do not treat this file as a design doc.

## Current Status

- Current resource terminology:
  - `CResource`: bare resource, such as `memory(range)` or
    `composite(name, args)`.
  - `CResourceFact`: internal representation of a resource fact, such as
    `own(resource)` or `view(resource)`.
  - `CResourceAccessMode` / `ResourceAccessMode`: `Own` or `View`.
  - `ResourceContext`: concrete list of resource facts, with
    `try_compose_with_fact(s)`, `unchecked_with_fact(s)`,
    `satisfies_fact`, and `without_fact`.
- `docs/separation-logic.md` is the internal resource-logic design target.
- `docs/intermediate/permissions.md` is the main user-facing resource docs page.
- Composite resources currently use `contains`, `fact`, `observe`, `unfold`,
  and `fold`.
- `observe(resource)` is one-step and non-consuming. It exposes immediate pure
  facts and viewed immediate contained resource facts, not owned contained
  permissions.
- `separate(resource1, resource2)` and `contains(parent, child)` are Click pure
  facts. Composite observation/folded projection emits direct relation facts,
  and the kernel uses them to derive memory-specific `disjoint(...)`.
- `loadable(segment)` is now a Click proposition that lowers to the kernel
  loadability fact (`CMemoryLoadable`). Use it in composite `fact` clauses
  when a resource should expose memory loadability without exposing extra
  resource facts.
- Direct memory resource facts deterministically project loadability facts:
  `read(range)` and `write(range)` imply `loadable(range)`. Composite
  `observe(...)`/folded projection exposes this for immediate contained memory
  resources without recursive search.
- Initial proof setup now materializes folded composite resource cells before
  lowering proposition requirements, so requirements like `index < owner->len`
  can use facts backed by a composite resource required by the same function.
- Missing-fact diagnostics now name the required pure/resource fact and print
  the available pure facts and resource facts. Execution obligations are also
  reported as missing pure facts with the same context format.
- Proof-step replay now has an explicit execution point. The supported points
  are function entry, straight-line statement entry via `execute_step()` or
  `execute_until(statement(N))`, and function exit via `execute_step()` or
  `execute_rest()`. `symbolic_execute()` is still accepted as a legacy spelling
  for `execute_rest()`.
- The current owner-buffer pressure tests are:
  - `mdtests/composite_resource_owned_buffer_len_cap_data.md`
  - `mdtests/composite_resource_owned_buffer_observe_len.md`
  - `mdtests/composite_resource_owned_buffer_get.md`
  - `mdtests/composite_resource_owned_buffer_observe_indexed.md`
  - `mdtests/composite_resource_owned_buffer_set.md`
  - `mdtests/composite_resource_owned_buffer_clear.md`
  - `mdtests/composite_resource_execute_until_direct_mutate.md`
  - `mdtests/composite_resource_execute_step_direct_mutate.md`
  - `mdtests/composite_resource_view_then_mutate.md`
  - `mdtests/composite_resource_observe_nested_separate_contains.md`
  - `mdtests/composite_resource_owned_buffer_nested_hidden_disjoint_gap.md`
- The latest verification pass recorded here:
  - `cargo fmt`
  - `cargo check`
  - `cargo test`
  - `cargo fmt -- --check`
  - `target/tools/bin/mdbook build`
  - `git diff --check`

## Open Questions

1. **General separation facts**

   Click now has pure resource-algebra facts `separate(resource1, resource2)`
   and `contains(parent, child)`. Composite resources project direct
   `contains(parent, child)` facts for owned contained resources and direct
   `separate(child1, child2)` facts for owned sibling resources. The kernel
   proves `contains` transitively, projects `separate` through contained
   children, and derives memory `disjoint(...)` from
   `separate(memory(...), memory(...))`.

2. **Hidden footprint projection**

   Folded composite resources currently expose one-step pure facts/resource
   facts plus direct `contains`/`separate` relation facts. A chain of explicit
   `observe(...)` steps can now dig into nested composite resources and use
   those theorem rules; see
   `mdtests/composite_resource_observe_nested_separate_contains.md`. The open
   design question is how much of that should be summarized or automated for
   nested composite resources.

3. **Allocation/provenance**

   Future allocation resources need a story for freshness and provenance.
   Decide what evidence should justify inferred non-aliasing between newly
   allocated memory, owner structs, and derived buffers.

4. **Composite-resource ergonomics**

   The `owned_buffer_with_room(owner)` example works, but keep using concrete
   mdtests to test whether explicit `unfold`/`fold` proof steps become too
   noisy before adding scoped or automated proof steps. The current
   `execute_until_direct_mutate` and `execute_step_direct_mutate` tests
   demonstrate the first straight-line execution-point slices. The
   `view_then_mutate` test covers automatic one-step entry projection for
   `views composite(...)` resources. The `observe_indexed` test passes
   and covers observing a field-dependent backing-array resource enough for
   indexed reads through the loaded pointer. `mdtests/composite_resource_loadable_fact.md`
   is the smaller passing case for direct-pointer `fact loadable(...)`
   projection.

5. **Read/write semantics**

   `read(...)` is the core/view of `write(...)` for memory. `write(...)` is
   still required to stabilize resource facts that read mutable memory. The
   exact long-term story for read stability, write exclusivity, and future
   allocation/free authority is still open.

## Useful Next Tasks

- Decide whether nested hidden footprints should be summarized by explicit
  resource-family footprint views, left as explicit observation chains, or
  handled by a bounded proof step. Avoid recursive default `auto` expansion
  because large composite resources could make that expensive or unpredictable.
  The expected-fail mdtest above and the passing
  `observe_nested_separate_contains` test are the pressure tests.
- Keep pressure-testing composite resources with realistic examples before
  adding scoped unfold/fold syntax or automation.
- Extend `execute_step()` beyond the current straight-line statement slice when
  branch, loop, or modular-call stepping becomes important.
- If hidden footprint summaries are added, make them deterministic one-step
  proof data first; leave `auto` heuristics for a later pass.

## Useful Commands

- `cargo test`
- `cargo fmt`
- `target/tools/bin/mdbook build`
- `scripts/mdbook-serve.sh`
- `git diff --check`
