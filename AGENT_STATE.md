# Agent State

Last updated: 2026-07-03.

## Repository State

- This file is a working handoff note, not canonical documentation. Check
  `git status --short --untracked-files=all` for the current worktree state.
- The docs are built with mdBook. `scripts/mdbook-serve.sh` installs a pinned
  repo-local mdBook into `target/tools` if needed and then runs `mdbook serve`.
- The most recent verification pass recorded here was:
  - `cargo fmt`
  - `cargo test`
  - `git diff --check`
  - `target/tools/bin/mdbook build`
- `scripts/mdbook-serve.sh --port 4000` successfully installed mdBook 0.4.52
  into `target/tools`, built the book, and served it at
  `http://localhost:4000`; the foreground serve process was then stopped.
- Those checks most recently passed after standardizing composite-resource
  proof steps on `unfold(...)`/`fold(...)`, making
  `observe(resource)` one-step and non-consuming, adding visible-write
  `disjoint(...)` projection, direct hidden-write `disjoint(...)` projection
  for folded composite resources, rejection of provably overlapping visible
  writes, improved composite-resource fact diagnostics, and the related
  docs/mdtests.
- Failed composite-resource fact framing diagnostics now keep the original
  one-line error and add notes about contained resources considered and scalar
  fact assumptions available.
- Folded composite resources now project their immediate fact view while the
  abstract resource token is held. Their contained resources/permissions remain
  hidden until an explicit `unfold(...)`.
- `observe(resource);` is a non-consuming proof step that projects one view
  step of a held composite resource. It exposes immediate facts and viewed
  immediate contained resources without exposing owned permissions; nested
  composite facts need another explicit `observe(...)`.
- `docs/intermediate/permissions.md` now has a worked composite-resource
  section organized around the three local proof steps: `observe`, `unfold`,
  and `fold`.
- `mdtests/composite_resource_owner_buffer_hidden_disjoint_projection.md`
  records that hidden contained writes imply folded-resource `disjoint(...)`
  facts without exposing hidden permissions.
- `mdtests/composite_resource_owned_buffer_len_cap_data.md` records a
  len/cap/data owned-buffer push shape. It uses a stronger
  `owned_buffer_with_room(owner)` pre-state resource and folds back to
  `owned_buffer(owner)` after mutation.
- The signed-order solver now knows the universal int32 bounds:
  `INT_MIN <= x`, `x <= INT_MAX`, `!(x < INT_MIN)`, and `!(x > INT_MAX)`.
  This lets `owner->len < owner->cap` imply enough upper-bound information to
  prove `owner->len + 1` does not overflow.
- The old pre-composite terminology has been renamed to "composite resource"
  in code/docs/mdtests. Internally, `ResourceDefinition` now has an optional
  `CompositeResourceBody`; mdtest filenames use `composite_resource_*`.

## Current Design Thread

We are in the middle of designing Click's resource logic.

`docs/separation-logic.md` is now the internal design target for the
Iris-inspired resource model. It says Click is not yet implemented as a full
resource algebra, but should refactor toward explicit resource state `M`,
`empty`, `compose`, `valid`, `core`, and observable facts. It also records that
the Click surface has `read(...)`, `write(...)`, declared token resources, and
composite resources. Internally, the bare resources are `CResource` values, and
the resource algebra elements are `CResourceElement::View(resource)` or
`CResourceElement::Own(resource)`.
The first code refactor toward that model added
`ResourceContext::validity_error(...)` / `ResourceContextValidityError` for
explicit resource-state validity checks. Checked composition now goes through
`ResourceContext::try_compose_with_element(s)(...)`, which validates the raw
combined resource state before normalizing it. Function-call transfer,
function resource-context evaluation, `unfold(...)`, and `fold(...)` now use
checked composition when adding resources.
Raw context construction is now explicitly named
`unchecked_with_element(s)(...)`; it remains for tests and assumption-free
lowering/materialization paths that build provisional contexts before
proposition assumptions are available.
The next refactor added `CResourceElement::core()`. The latest version makes
this generic: `core(own(resource)) = view(resource)` and
`core(view(resource)) = view(resource)` for memory, token, and composite
resources. Read entailment, read consumption, and memory-read authorization now
route through that resource-element core operation.
The latest resource refactor keeps the Click surface syntax `read(...)` /
`write(...)`, but changes the internal kernel resource shape to
`CResourceElement::View(CResource::Memory(range))` for reads and
`CResourceElement::Own(CResource::Memory(range))` for writes. Declared
bodyless resources lower to token resources, and body-backed resources lower
to composite resources.
The latest terminology cleanup makes `CResource` mean the bare resource,
`CResourceElement` mean an algebra element such as `own(resource)` or
`view(resource)`, and `CResourceAccessMode` / `ResourceAccessMode` mean the
`Own`/`View` mode. `ResourceContext` now stores `elements` and exposes
element-oriented methods such as `try_compose_with_element(s)`,
`unchecked_with_element(s)`, `satisfies_element`, and `without_element`.
The next observable-facts refactor added
`ResourceContext::observable_facts(...)`, which checks resource-state validity
and returns ordinary facts derived from the concrete resource context. Today it
routes owned-memory `disjoint(...)` facts through this interface. Proof-layer
observable-facts projection now calls this unconditionally, so projection also
validates the resource context when no facts are produced. Composite-resource
observable-facts projection groups contained resource-context observable facts
with declared `fact` clauses; the proof layer still handles
resource-definition substitution and memory materialization.

The current settled terminology is:

- A `code region` is a syntactic region of C code, such as `loop(0)`.
- A `program point` is a syntactic point associated with a region, such as a
  loop entry point.
- A `visit` is a dynamic execution occurrence of a program point. Visits are
  conceptual for now, not first-class Click expressions.
- A resource is something the proof/resource context can `hold`.
- A composite resource may expose `fact` clauses while its abstract token is
  held folded, and while it is unfolded.
- `own`/`view` are internal access modes. The new surface verbs are
  `owns`, `views`, `consumes`, and `produces`; old `requires`/`ensures`
  resource clauses are still accepted for compatibility.
- Resource facts are not called invariants. Loop `invariant` remains a separate
  concept.

The current philosophical model for resources is:

- Resources are a way to decompose mutable program state into smaller logical
  pieces.
- Holding a resource can mean several things:
  - it grants permission to do something;
  - it must be consumed to do something;
  - it bundles other resources;
  - it makes facts available while the resource is held.
- `read` and `write` are the built-in first-layer memory resource families.
- User-defined resources are needed for concepts that are not just memory
  ownership, such as "this callback may still be called once".
- "hold" is the preferred descriptive verb for now. "own" is too suggestive of
  a one-owner model, though it may still be natural for some specific resources.

## Implemented Resource Pieces

Click currently has:

- Resource contexts.
- Built-in memory resources:
  - `read(p[a..b])`
  - `write(p[a..b])`
- Function specs that require and ensure resources.
- Function calls that consume required resources unless returned.
- Basic resource diagnostics for missing or duplicate resources.
- Token resources.
- Duplicate owned token/composite resource rejection.
- Composite resources with:
  - `contains ...;`
  - `fact ...;`
  - explicit `observe(resource);`
  - explicit `unfold(resource);`
  - explicit `fold(resource);`
- Resource facts are projected while the abstract resource token is held folded
  for one composite-resource layer, and are also available
  while the resource is unfolded.
- `observe(resource);` explicitly projects a held composite resource's fact
  view before execution. It is useful when a proof script should record the
  non-destructive, one-step fact-projection step.
- `fold(...)` proves the facts, consumes the contained resources, and returns
  the abstract resource token.
- Resource fact validation checks that facts which read mutable memory are backed
  by contained `write(...)` permission, not merely `read(...)`.
- Resource fact validation can use scalar facts from the same fact clause to
  justify symbolic indexed reads, for example `0 <= k and k < n and p[k] == 0`.
- Resource facts can include `disjoint(...)` range facts. This has standalone
  mdtest coverage in `mdtests/composite_resource_disjoint_fact.md` as well as
  the owner-buffer pressure test.
- `read(...)` is the stable read/core view for memory resources:
  internally, `core(own(memory(range))) = view(memory(range))` and
  `core(view(memory(range))) = view(memory(range))`.
  The kernel routes read entailment, read consumption, and external-load
  permission checks through `CResourceElement::core()`.
- Visible `write(...)` resources imply `disjoint(...)` facts for their ranges;
  direct hidden contained `write(...)` resources do the same while a composite
  resource is folded; `read(...)` resources do not imply disjointness. Folded
  resource permissions remain hidden.
- Provably overlapping visible `write(...)` resources are rejected.
- Holding a covering `read(...)` or `write(...)` resource discharges external
  load validity obligations for the covered access. Holding `write(...)`
  similarly discharges external store validity obligations.

## Recent Cleanup

The most recent separation-logic cleanup narrowed the first-layer resource
surface to `read(...)`, `write(...)`, declared token resources, composite
resources, composition, and facts. Resource definitions now use
`resource name(...)` directly; the old prefixed resource keyword form is gone.
Deallocation authority was removed from the active Click/C0/kernel surface and
is parked for a later allocation lifecycle layer.

The current refactor added `owns`, `views`, `consumes`, and `produces` as
resource verbs in function specs. Internally, declared resources are now
classified as either token resources or composite resources, and both use the
same `Own`/`View` access mode as memory resources. Duplicate owned token or
composite resources are rejected; duplicate views can normalize harmlessly.
The latest proof-step cleanup standardized resource proof steps on
`unfold`/`fold`; predicate `unfold(name)` remains non-consuming, while resource
`unfold(name(args))` consumes the owned composite and exposes its body.

An earlier terminology cleanup changed composite-resource clauses from
`invariant` to `fact`.

Example current syntax:

```click
resource uncalled(flag: int32*) {
    contains write(flag[0..1]);
    fact flag[0] == 0;
}
```

The old resource-body `invariant` spelling should be considered gone. Loop
invariants still use `invariant`.

## Struct And Memory Support

Recent work also improved struct/pointer support enough to start testing
resource designs against owner-buffer examples.

Current support includes:

- Struct definitions and field access in C parsing/lowering.
- Pointer-valued struct field loads in symbolic reasoning.
- Struct field validity/read support in the memory model.
- Basic composite-resource examples involving structs.

The important pressure-test examples are:

- `mdtests/composite_resource_owner_buffer_field_dependent.md`
- `mdtests/composite_resource_owner_buffer_hidden_disjoint_projection.md`

These examples exercise the desired ergonomic shape and are currently passing.
The field-dependent resource can package explicit shape facts, and its hidden
contained writes now expose derived folded-resource non-aliasing facts.

## Known Open Design Issue

The owner-buffer pressure tests now work with both explicit facts and direct
hidden-owned-memory-derived disjointness: a composite resource can contain
permissions derived from `owner->data` and `owner->len`, and a folded instance
exposes derived non-aliasing facts for those direct contained writes.

The broader open design issue is how much of this should remain explicit and
how much should become derived from memory-resource/allocation structure.

The shape now supported is:

- A struct has fields such as `owner->data` and `owner->len`.
- A resource over `owner` should be able to contain permissions for the buffer
  derived from `owner->data`.
- The resource should also carry facts tying the owner fields to the buffer
  shape, for example length/capacity facts.
- Packing the resource proves those facts and repackages the contained
  resources.

The unresolved part is no longer basic syntax for non-aliasing facts, whether
folded resources expose facts, or whether visible writes imply disjointness.
Remaining design questions include:

- How broad should hidden composite-resource footprint projection be for
  disjointness beyond direct contained writes, for example cross-resource hidden
  footprints or allocation provenance?
- How much should `read` or `write` imply about stability?
- What allocation/provenance structure, if any, should justify inferred
  non-aliasing facts?

This is still the next real design frontier, but the explicit-fact slice,
one-step fact views, visible-write-derived disjointness, direct
hidden-owned-memory-derived disjointness, and explicit fact observation are
implemented.

## Useful Next Steps

The owner-buffer examples now pass, `read(...)`/`write(...)` now both carry the
validity needed for covered external memory accesses, folded resources expose
one-step fact views, visible plus direct hidden contained `write(...)`
resources now imply disjointness, and `observe(...)` provides an explicit
fact-projection certificate step. Good next slices:

1. Decide how far hidden footprint disjointness should go beyond direct
   contained writes, especially across nested composite-resource footprints.
2. Decide what allocation/provenance evidence should prove freshness for future
   allocation resources.
3. Consider a scoped unfold/fold proof step only if examples show explicit
   `unfold(...)`/`fold(...)` is creating avoidable proof noise.
4. Keep tightening owner-buffer ergonomics through concrete mdtests before
   adding larger abstractions.

Keep forcing each resource-logic feature through a concrete mdtest before
adding broader abstraction.

## Other Design Threads Already Touched

### Documentation

The docs were refactored into a mdBook-style progression:

- Basic Click: what Click is, specs, propositions, proof scripts.
- Intermediate Click: memory, permissions, pure Click functions, spec state,
  resources.
- Advanced Click: internals, testing, roadmap, contributor-oriented material.

The beginner docs are structurally present but probably still need a human pass
for tone and teaching quality.

### `let`

Click has Rust-style `let` syntax in specs/propositions:

```click
let name: Type = expr;
```

Type inference is intended where possible. There is also `let ... where` for
choosing a value satisfying a proposition. We decided not to call this "ghost"
because all Click code is already spec-only relative to C runtime execution.

### `at`

The basic design direction is that `at(...)` is really about referring to values
at visits relative to the current proof context. The current implementation is
limited and should be understood as an initial form, not the final model of
visits.

The conceptual issue:

- A program point can be visited many times.
- `at(program_point, expr)` is ambiguous unless it selects a visit.
- For now, the useful restricted model is "the relevant previous/entry visit
  implied by the current context."

This will likely need a more explicit `VisitSelector`-style concept later.

### Pure Theorems

Pure theorem definitions and theorem application exist. We decided:

- Use `theorem`, not separate `lemma`.
- Theorems should be pure and should not transform resources.
- Resource-transforming behavior belongs in function/resource specs or explicit
  resource operations, not theorem application.

Some small stdlib theorem support exists for common pure proof needs.

### Mutable Spec State

General first-class mutable spec/model state does not exist yet. We have avoided
adding it prematurely because many motivating examples can be handled better by
resource logic.

If needed later, spec state should be designed after the resource model is
clearer.

## Terms To Keep Consistent

Use:

- `resource context`
- `hold a resource`
- `resource fact`
- `contained resource`
- `composite resource`
- `resource`
- `code region`
- `program point`
- `visit`

Avoid:

- Calling resource facts "invariants".
- Using the old pre-composite resource terminology.
- Using "own" for all resources unless discussing a genuinely ownership-like
  resource.
- Treating "proof state" as an object that Click predicates can refer to.

## Current Mental Model Of `read`, `write`, And Stability

The existing implementation treats `read` and `write` as the first-layer memory
resources, but the exact semantic story is still not fully polished.

Important points:

- `read` authorizes inspection and carries validity for covered external loads.
- `write` authorizes mutation, carries validity for covered external stores,
  and is the permission currently required for a resource fact that reads memory.
- `read` alone is not enough to make a memory-reading resource fact stable,
  because another holder could write the same memory.
- Free/deallocation authority is deliberately parked for a later allocation
  lifecycle layer.

The unresolved part is how much non-aliasing/stability should be inferred from
these permissions and how much should be explicit facts.

## Good Commands

- Run all tests: `cargo test`
- Format: `cargo fmt`
- Serve docs with repo-local mdBook install: `scripts/mdbook-serve.sh`
- Check whitespace: `git diff --check`

## Suggested Immediate Next Task

Design the next owner-buffer ergonomics slice around inferred versus explicit
non-aliasing.

Recommended pressure test:

1. Write a small expected-fail mdtest for the owner-buffer shape without an
   explicit `fact disjoint(...)`.
2. Decide what evidence should imply that the owner fields and derived buffer do
   not overlap: allocation provenance, exclusive `write(...)` resources, or an
   explicit fact that users must keep writing.
3. Only after that, implement the narrow inference rule or keep the explicit
   fact model and improve proof ergonomics where examples show real friction.
