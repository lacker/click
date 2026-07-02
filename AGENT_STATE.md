# Agent State

Last updated: 2026-07-02.

## Repository State

- Working tree was clean when this file was written.
- The docs are built with mdBook. `mdbook serve` is the normal build-and-serve
  command.
- The most recent verification pass I ran was:
  - `cargo fmt`
  - `cargo test`
  - `git diff --check`
- `mdbook build` could not be run in this environment because `mdbook` was not
  installed.
- Those checks passed after adding resource-packaged `disjoint(...)` facts for
  the owner-buffer example.

## Current Design Thread

We are in the middle of designing Click's resource logic.

The current settled terminology is:

- A `code region` is a syntactic region of C code, such as `loop(0)`.
- A `program point` is a syntactic point associated with a region, such as a
  loop entry point.
- A `visit` is a dynamic execution occurrence of a program point. Visits are
  conceptual for now, not first-class Click expressions.
- A resource is something the proof/resource context can `hold`.
- A resource may expose `fact` clauses while it is opened or held.
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
- `read`, `write`, and `free` are the built-in memory resource families.
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
  - `free(p[a..b])`
- Function specs that require and ensure resources.
- Function calls that consume required affine resources unless returned.
- Basic resource diagnostics for missing or duplicate resources.
- Affine named resources.
- Duplicate identical affine-token rejection.
- Represented resources with:
  - `contains ...;`
  - `fact ...;`
  - explicit `open(resource);`
  - explicit `close(resource);`
- Resource facts are exposed by `open(...)`.
- `close(...)` proves the facts, consumes the contained resources, and returns
  the abstract resource token.
- Resource fact validation checks that facts which read mutable memory are backed
  by contained `write(...)` permission, not merely `read(...)`.
- Resource fact validation can use scalar facts from the same fact clause to
  justify symbolic indexed reads, for example `0 <= k and k < n and p[k] == 0`.
- Resource facts can include `disjoint(...)` range facts.
- Holding a covering `read(...)` or `write(...)` resource discharges external
  load validity obligations for the covered access. Holding `write(...)`
  similarly discharges external store validity obligations.

## Recent Cleanup

The most recent terminology cleanup changed represented-resource clauses from
`invariant` to `fact`.

Example current syntax:

```click
affine resource uncalled(flag: int32*) {
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
- Basic represented-resource examples involving structs.

The important pressure-test example is:

- `mdtests/represented_resource_owner_buffer_field_dependent.md`

That example is intentionally the desired ergonomic shape and is currently
passing. It packages the needed non-aliasing fact between the owner fields and
the derived buffer as a `fact disjoint(...)` clause.

## Known Open Design Issue

The owner-buffer pressure test now works for the explicit-fact design: a
represented resource can contain permissions derived from `owner->data` and
`owner->len`, and can package an explicit `disjoint(...)` fact for the derived
buffer.

The broader open design issue is how much of this should remain explicit and
how much should become derived from memory-resource/allocation structure.

The shape now supported is:

- A struct has fields such as `owner->data` and `owner->len`.
- A resource over `owner` should be able to contain permissions for the buffer
  derived from `owner->data`.
- The resource should also carry facts tying the owner fields to the buffer
  shape, for example length/capacity facts.
- Closing the resource proves those facts and repackages the contained
  resources.

The unresolved part is no longer basic syntax for non-aliasing facts. Remaining
design questions include:

- Should common non-aliasing facts remain ordinary explicit `fact disjoint(...)`
  clauses, or should some be derived from `write(...)`/allocation resources?
- How much should `read` or `write` imply about stability?
- What exactly should it mean for a resource fact to remain true while the
  resource is held but closed?

This is still the next real design frontier, but the first explicit-fact slice
is implemented.

## Useful Next Steps

The owner-buffer example now passes, and `read(...)`/`write(...)` now both
carry the validity needed for covered external memory accesses. Good next
slices:

1. Add a smaller regression mdtest for `fact disjoint(...)` that is independent
   of structs, if more coverage feels useful.
2. Explore whether any non-aliasing facts can be inferred from allocation or
   stronger memory-resource structure instead of written explicitly.
3. Improve diagnostics for failed resource fact framing so aliasing failures say
   which write may alias which fact read.
4. Decide whether any of the explicit `fact disjoint(...)` clauses in represented
   resources should become derived facts from allocation/resource structure.

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
- `represented resource`
- `affine resource`
- `code region`
- `program point`
- `visit`

Avoid:

- Calling resource facts "invariants".
- Using "own" for all resources unless discussing a genuinely ownership-like
  resource.
- Treating "proof state" as an object that Click predicates can refer to.

## Current Mental Model Of `read`, `write`, And Stability

The existing implementation treats `read`, `write`, and `free` as resources, but
the exact semantic story is still not fully polished.

Important points:

- `read` authorizes inspection and carries validity for covered external loads.
- `write` authorizes mutation, carries validity for covered external stores,
  and is the permission currently required for a resource fact that reads memory.
- `read` alone is not enough to make a memory-reading resource fact stable,
  because another holder could write the same memory.
- `free` is affine/consumable in practice because freeing twice should fail.

The unresolved part is how much non-aliasing/stability should be inferred from
these permissions and how much should be explicit facts.

## Good Commands

- Run all tests: `cargo test`
- Format: `cargo fmt`
- Serve docs with repo-local mdBook install: `scripts/mdbook-serve.sh`
- Check whitespace: `git diff --check`

## Suggested Immediate Next Task

Run `scripts/mdbook-serve.sh` once to smoke-test the docs with the repo-local
mdBook wrapper. The first run may download mdBook into `target/tools`.

After that, the next resource-design slice should probably be a small,
standalone mdtest for `fact disjoint(...)` or diagnostics for failed represented
resource fact framing.
