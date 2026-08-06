# Refactor large verifier modules along proof-model boundaries

## Motivation

Several Click implementation files have accumulated enough unrelated
responsibilities that navigation and review are becoming difficult:

- `src/lang/click/proof.rs` is about 27,000 lines;
- `src/kernel/api.rs`, `src/kernel/assumptions.rs`,
  `src/lang/click/checking.rs`, and `src/lang/click/lowering.rs` are each
  roughly 5,000–9,000 lines;
- `src/bin/click-profile.rs` is about 3,000 lines; and
- the Click-language and kernel test modules are each about 10,000 lines.

File length alone is not the problem. `proof.rs`, in particular, combines pure
theorem checking, smart-tactic planning, certificate construction, certificate
replay, execution-frontier management, Surface Click synthesis, statement
snapshot tracking, exit-claim finalization, and composite-resource laws.
`replay_linear_tactics` and `finish_ordered_proof_replay` are each roughly
2,000 lines and coordinate many parallel arguments and pieces of mutable state.
This makes the important boundaries between search, proof plans, surface
certificates, and fresh replay harder to see and enforce.

## Goal

Make implementation ownership follow Click's conceptual proof model. A reader
should be able to locate smart planning, deterministic replay, surface
certificate synthesis, execution, and resource behavior without reading one
monolithic module.

The refactoring should preserve and clarify the shared proof-producing
architecture. In particular, planning and replay should become visibly
separate stages with an explicit data boundary between them; statement
snapshots and their source-layout identities are part of that boundary.

## Non-goals

- Do not change proof semantics, tactic heuristics, budgets, accepted C, or
  Surface Click syntax merely to make extraction easier.
- Do not combine this cleanup with vector work or another language feature.
- Do not split files mechanically if the result is only a web of broadly
  visible helpers and circular dependencies.
- Do not attempt a repository-wide reorganization in one commit.
- Do not treat every large file as equally urgent. A cohesive reasoning engine
  may legitimately remain larger than a miscellaneous orchestration module.

## Candidate boundaries

### Click proof orchestration

The eventual shape may resemble:

```text
src/lang/click/proof/
  mod.rs
  pure.rs
  replay.rs
  execution.rs
  surface.rs
  resources.rs
  finalization.rs
```

The names are provisional; the important boundaries are responsibilities, not
this exact directory layout.

Before moving large regions mechanically, introduce an owned replay/session
object that holds the environments and mutable proof context currently passed
through long argument lists. Break the giant tactic dispatcher into focused
handlers operating on that session. Separate exit-claim finalization from
linear tactic replay.

When the structured smart proof plan is implemented, it should sit between
planning and replay rather than becoming another parallel collection of state
inside `proof.rs`.

### Click checking

`src/lang/click/checking.rs` already has relatively clear domains and is a good
first production extraction candidate:

- predicate evaluation and unfolding;
- proposition simplification;
- effect checking; and
- contract-expression and outcome evaluation.

Keep a small façade when that avoids widespread import churn.

### Kernel API

`src/kernel/api.rs` currently contains several distinct subsystems:

- memory-DAG and snapshot-equivalence reasoning;
- public C AST/value builder helpers;
- symbolic-execution entry points; and
- contract/path certification.

Move these behind the existing `kernel` public façade so callers do not need to
know the internal file layout. Preserve the kernel's theorem-construction
boundary during every move.

### Other bounded extractions

- Split `src/bin/click-profile.rs` into argument/runner, profile model and
  collection, and report rendering.
- Split `src/lang/click/lowering.rs` around contract substitution, source
  execution layout, resource lowering, and expression/proposition lowering
  where dependencies permit.
- Divide `src/lang/click/tests.rs` and `src/kernel/tests.rs` into topical test
  modules with shared helpers kept narrow.

### Assumptions engine

Do not begin with `src/kernel/assumptions.rs`. Most of it is one interconnected
reasoning implementation. First identify stable theory-level interfaces—for
example equality, signed order, memory/range reasoning, and memo/budget
control. Extract only when doing so reduces coupling rather than spreading
private implementation details through `pub(super)` APIs.

## Recommended order

Each item is an independently comprehensible, behavior-preserving chunk:

1. Split the large test modules by topic.
2. Split `click-profile` collection/model/rendering.
3. Divide `checking.rs` along its existing domain boundaries.
4. Introduce an owned proof replay/session context and extract focused tactic
   handlers.
5. Separate proof planning, replay, surface synthesis, execution, resources,
   and finalization as their interfaces become explicit.
6. Split `kernel/api.rs` behind its unchanged public façade.
7. Reassess `lowering.rs` and `assumptions.rs` after the higher-level
   boundaries settle.

The order is guidance, not a requirement to finish the entire list. Prefer the
next extraction with an obvious boundary and useful reduction in coupling.

## Acceptance criteria for each chunk

- The commit is primarily file/module movement plus narrow interface cleanup,
  not a feature or heuristic change.
- The extracted module has one coherent responsibility that can be described
  without listing unrelated exceptions.
- Visibility is no broader than necessary; a large increase in `pub(super)` is
  a reason to reconsider the boundary.
- Search, certificate generation, replay, and kernel certification continue to
  use the same authority boundaries.
- Formatting, the relevant focused tests, the full library tests, and the
  applicable example/mdtest gates pass within normal budgets.
- Any unexpected verifier slowdown, expansion disagreement, or changed proof
  result is treated as a regression, not accepted as cleanup fallout.
- Land and push each independently green chunk separately.

Delete this issue when the remaining large modules are either decomposed along
stable boundaries or deliberately documented as cohesive enough to keep.
