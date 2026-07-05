# Agent State

Last updated: 2026-07-05.

This is a short handoff note for open work only. Canonical documentation lives
in `docs/`; do not treat this file as a design doc.

## Current Status

- Current resource terminology:
  - `CResource`: bare resource, such as `memory(range)` or
    `composite(name, args)`.
  - `CResourceElement`: algebra element, such as `own(resource)` or
    `view(resource)`.
  - `CResourceAccessMode` / `ResourceAccessMode`: `Own` or `View`.
  - `ResourceContext`: concrete list of resource elements, with
    `try_compose_with_element(s)`, `unchecked_with_element(s)`,
    `satisfies_element`, and `without_element`.
- `docs/separation-logic.md` is the internal resource-logic design target.
- `docs/intermediate/permissions.md` is the main user-facing resource docs page.
- Composite resources currently use `contains`, `fact`, `observe`, `unfold`,
  and `fold`.
- `observe(resource)` is one-step and non-consuming. It exposes immediate facts
  and viewed immediate contained resources, not owned contained permissions.
- Proof-step replay now has an explicit execution point. The supported points
  are function entry, straight-line statement entry via
  `execute_until(statement(N))`, and function exit via `execute_rest()`.
  `symbolic_execute()` is still accepted as a legacy spelling for
  `execute_rest()`.
- The current owner-buffer pressure tests are:
  - `mdtests/composite_resource_owned_buffer_len_cap_data.md`
  - `mdtests/composite_resource_owned_buffer_observe_len.md`
  - `mdtests/composite_resource_owned_buffer_get.md`
  - `mdtests/composite_resource_owned_buffer_observe_indexed_gap.md`
  - `mdtests/composite_resource_owned_buffer_set.md`
  - `mdtests/composite_resource_owned_buffer_clear.md`
  - `mdtests/composite_resource_execute_until_direct_mutate.md`
  - `mdtests/composite_resource_view_then_mutate_gap.md`
  - `mdtests/composite_resource_owned_buffer_nested_hidden_disjoint_gap.md`
- The latest verification pass recorded here:
  - `cargo fmt`
  - `cargo test`
  - `target/tools/bin/mdbook build`
  - `git diff --check`

## Open Questions

1. **General separation facts**

   `disjoint(range1, range2)` is memory-specific, but it is really one
   observable fact produced by valid composition of resource elements. We do
   not yet have a general user-visible or internal abstraction for
   "separateness" beyond `ResourceContext::observable_facts(...)`.

2. **Hidden footprint projection**

   Folded composite resources currently expose one-step facts and direct
   hidden-write-derived `disjoint(...)` facts. The open design question is how
   far this should go for nested composite resources or cross-resource hidden
   footprints.

3. **Allocation/provenance**

   Future allocation resources need a story for freshness and provenance.
   Decide what evidence should justify inferred non-aliasing between newly
   allocated memory, owner structs, and derived buffers.

4. **Composite-resource ergonomics**

   The `owned_buffer_with_room(owner)` example works, but keep using concrete
   mdtests to test whether explicit `unfold`/`fold` proof steps become too
   noisy before adding scoped or automated proof steps. The current
   `execute_until_direct_mutate` test demonstrates the first straight-line
   execution-point slice. The `view_then_mutate_gap` test now documents the
   next modular-call gap: a callee with `views composite(...)` does not yet
   execute with observed contained memory views. The
   `observe_indexed_gap` test documents that observing a field-dependent
   backing-array resource is not yet enough for indexed reads through the
   loaded pointer.

5. **Read/write semantics**

   `read(...)` is the core/view of `write(...)` for memory. `write(...)` is
   still required to stabilize resource facts that read mutable memory. The
   exact long-term story for read stability, write exclusivity, and future
   allocation/free authority is still open.

## Useful Next Tasks

- Decide whether nested hidden footprints should be summarized recursively,
  via explicit resource-family footprint views, or left as explicit
  `fact disjoint(...)` obligations. The expected-fail mdtest above is the
  pressure test.
- Keep pressure-testing composite resources with realistic examples before
  adding scoped unfold/fold syntax or automation.
- Consider a scoped or step-bounded execution proof form if view-call-then-mutate
  examples become important enough to support beyond the current straight-line
  `execute_until(statement(N))` slice.
- Decide whether `observe` should materialize dependent contained resource views
  strongly enough to support owner-field-derived backing-array reads.
- If hidden footprint summaries are added, make them deterministic one-step
  proof data first; leave `auto` heuristics for a later pass.

## Useful Commands

- `cargo test`
- `cargo fmt`
- `target/tools/bin/mdbook build`
- `scripts/mdbook-serve.sh`
- `git diff --check`
