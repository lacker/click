# Spec State

Spec state is extra state used by the specification and proof. It is not stored
in the C program, but it helps the verifier describe facts about the C program.

Other verification systems often call this "ghost" state because proof-only
variables live in the same language as executable variables. Click already
separates `.c` runtime code from `.click` specification code, so "not compiled"
is not the important distinction. The useful distinction is whether a Click
name is a simple immutable abbreviation or extra proof/model state across
program points.

Click does not yet have general first-class mutable spec state. It does have a
small resource context for viewed and owned memory resources,
described in [Permissions](permissions.md). This page records the intended
place of the broader feature so future permission and ownership work has a
clean target.

## Why Spec State Matters

Some useful facts are not directly stored in C memory.

Examples:

- the logical length of a null-terminated string,
- which object is responsible for freeing a heap allocation,
- how much permission a caller has for a memory range,
- a reference-count ownership invariant,
- or a relationship between two concrete fields that should be treated as one
  abstract state.

These facts are about the C program, but they are not ordinary C variables.
They belong in the specification layer.

Do not confuse this with `let`:

```click
let len: int32 = strlen_model(src);
```

That is an immutable abbreviation for a specification expression. It is useful,
but it is not mutable state.

## What Click Has Today

Click already has a few spec-only mechanisms:

- `old(...)` lets specs refer to function-entry state.
- `at(statement(N).entry, ...)` and `at(statement(N).exit, ...)` can name
  complete statement-state snapshots recorded by deterministic proof
  execution, including memory and C local values. Their second argument may be
  an expression or a complete proposition such as `loadable(p[0..n])`.
- labels give names to requirements and guarantees.
- predicates package abstract facts.
- `let ... where` introduces immutable witnesses in proposition clauses.
- `choose` introduces proof-local names from existential requirements.
- `witness` supplies proof-local values for existential goals.
- `views p[lo..hi]` and `owns p[lo..hi]` introduce resource facts for external
  memory accesses.
- `allocation(base, bytes)` records exclusive responsibility for a supported
  live heap allocation until it is returned or discharged by `free`.

These are useful, but they are not the same as first-class mutable spec state.

Across a function call, viewed resources are copyable and owned resources
follow the callee's resource verbs. `owns` receives and returns ownership;
`consumes` receives it; `produces` returns it. Click can split a covered
subrange out of a larger owned range and rejoin adjacent returned ranges.

## The Design Constraint

Spec state should feel like ordinary Click facts. A user should be able to
state, carry, unfold, and prove model facts without switching to a completely
different mental model.

This matters for permission logic. A resource fact may say that the current
proof state has read or write authority over some memory. Unlike pure facts,
some resource facts must not be copied freely. Click's viewed and owned memory
elements therefore live in a resource context rather than as
classical predicate facts.

## Relationship To Permission Logic

The current implementation starts with a narrow resource context before general
model variables. That lets Click pressure-test the permission machinery on the
central memory problem without committing to arbitrary global model state.

The intended layering is:

1. a small resource context for memory resource facts,
2. broader resource facts over memory locations, ranges, capabilities, and IO,
3. first-class model variables if examples need arbitrary spec state,
4. ownership predicates defined in libraries,
5. refcount and allocation examples that pressure-test those abstractions.

This keeps Click flexible. The kernel should not bake in json-c ownership as a
primitive concept. It should provide enough general spec-state and permission
support for libraries to define the ownership concepts they need.

## What Not To Assume Yet

Do not assume:

- that ownership is currently a built-in Click feature,
- that `loadable` means ownership,
- that `mutable` means permission to free,
- or that refcounting can be proved cleanly before the spec-state layer exists.

The current json-c refcount example intentionally stops before allocation,
release, and ownership transfer.
