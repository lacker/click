# Spec state

Spec state is extra state used by the specification and proof. It is not stored
in the C program, but it helps the verifier describe facts about the C program.

Other verification systems often call this "ghost" state because proof-only
variables live in the same language as executable variables. Click already
separates `.c` runtime code from `.click` specification code, so "not compiled"
is not the important distinction. The useful distinction is whether a Click
name is a simple immutable abbreviation or extra proof/model state across
program points.

Click does not yet have general first-class mutable spec state. It does have a
resource context for viewed and owned memory, allocation authority, and
user-defined resources, described in
[Resources and memory permissions](resources.md). This page
explains the boundary between those implemented mechanisms and more general
proof-only state.

## Why spec state matters

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

<!-- verified-example: mdtests/resource_count_predicate_snapshot.md -->
```click
let len: int32 = strlen_model(src);
```

That is an immutable abbreviation for a specification expression. It is useful,
but it is not mutable state.

## Supported specification state

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

## The design constraint

Spec state should feel like ordinary Click facts. A user should be able to
state, carry, unfold, and prove model facts without switching to a completely
different mental model.

This matters for memory-permission logic. A resource fact may say that the current
proof state has read or write authority over some memory. Unlike pure facts,
some resource facts must not be copied freely. Click's viewed and owned memory
elements therefore live in a resource context rather than as
classical predicate facts.

## Relationship to resource logic

The implemented specification layer has three kinds of state:

1. immutable specification terms, predicates, labels, and snapshots;
2. proof-local witnesses introduced by `choose` and supplied by `witness`; and
3. a resource context containing viewed, owned, allocation, abstract, and
   composite resource facts.

The resource context is stateful from the proof's perspective: calls and proof
steps can transfer, consume, produce, unfold, and fold its facts. That is enough
to model ownership protocols and the complete allocation, retain, release, and
free lifecycle in the refcount example. It is still not a general mutable ghost
store: users cannot declare an arbitrary spec variable and assign it at each
program point.

This boundary keeps the kernel independent of application-specific ownership
models. Libraries define those models with predicates and resources; the
kernel supplies their checked composition, transfer, and memory authority.

## Current boundaries

Keep these distinctions explicit:

- `let` is an immutable abbreviation, not mutable spec state.
- `loadable` proves memory safety and bounds; it does not grant access
  authority.
- `mutable` bounds a function's writes; it does not grant permission to access
  or free the named memory.
- A pure fact can be reused. An owned resource fact cannot be copied freely.
- Ownership protocols are expressible through resources, but arbitrary mutable
  ghost variables aren't supported.
