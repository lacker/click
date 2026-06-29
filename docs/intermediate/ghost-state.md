# Ghost State

Ghost state is specification-only state. It is not stored in the C program, but
it helps the verifier describe facts about the C program.

Click does not yet have first-class ghost variables or a full ghost-state
system. This page records the intended place of ghost state in the design so the
next feature work has a clean target.

## Why Ghost State Matters

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

## What Click Has Today

Click already has a few ghost-like mechanisms:

- `old(...)` lets specs refer to function-entry state.
- labels give names to requirements and guarantees.
- predicates package abstract facts.
- `choose` introduces proof-local names from existential requirements.
- `witness` supplies proof-local values for existential goals.

These are useful, but they are not the same as first-class ghost variables.

## The Design Constraint

Ghost state should feel like ordinary Click facts. A user should be able to
state, carry, unfold, and prove ghost facts without switching to a completely
different mental model.

This matters for future permission logic. A permission fact may say that a
proof has read, write, or free authority over some memory. That fact should be
represented as a proposition in the proof system, even if the proof rules for
using it are special.

## Relationship To Permission Logic

Permission logic should come after basic ghost state, not before it.

The intended layering is:

1. first-class ghost values and ghost facts,
2. permission facts over memory locations or ranges,
3. ownership predicates defined in libraries,
4. refcount and allocation examples that pressure-test those abstractions.

This keeps Click flexible. The kernel should not bake in json-c ownership as a
primitive concept. It should provide enough general ghost and permission support
for libraries to define the ownership concepts they need.

## What Not To Assume Yet

Do not assume:

- that ownership is currently a built-in Click feature,
- that `valid_range` means ownership,
- that `mutable` means permission to free,
- or that refcounting can be proved cleanly before the ghost-state layer exists.

The current json-c refcount example intentionally stops before allocation,
release, and ownership transfer.
