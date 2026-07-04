# Agent State

Last updated: 2026-07-03.

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
- The latest owner-buffer pressure test is
  `mdtests/composite_resource_owned_buffer_len_cap_data.md`.
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
   noisy before adding scoped or automated proof steps.

5. **Read/write semantics**

   `read(...)` is the core/view of `write(...)` for memory. `write(...)` is
   still required to stabilize resource facts that read mutable memory. The
   exact long-term story for read stability, write exclusivity, and future
   allocation/free authority is still open.

## Useful Next Tasks

- Add a short section to `docs/separation-logic.md` explaining that
  `disjoint(...)` is a memory-specific projection from valid resource-element
  composition, while the general separateness abstraction is intentionally not
  designed yet.
- Add an expected-fail mdtest for any owner-buffer shape we wish worked without
  an explicit `fact disjoint(...)`; use it to decide whether the missing
  evidence should come from allocation provenance, hidden writes, or explicit
  facts.
- Keep pressure-testing composite resources with realistic examples before
  adding new syntax.

## Useful Commands

- `cargo test`
- `cargo fmt`
- `target/tools/bin/mdbook build`
- `scripts/mdbook-serve.sh`
- `git diff --check`
