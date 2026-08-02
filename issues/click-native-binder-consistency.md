# Unify Click-native binder spelling

*Optional and lower priority than the proof-surface cleanup.*

## Problem

Click currently uses two parameter conventions for declarations that belong to
the Click language itself:

```click
theorem bounded(x: int32) { ... }
resource buffer(owner: struct buffer*) { ... }

function count(int32 p[], int32 lo, int32 hi) -> int32 { ... }
predicate sorted(int32 p[], int32 n) { ... }
forall (int32 k) { ... }
exists (int32 k) { ... }
```

The verified C function form has a good reason to use C declaration syntax: it
mirrors and is checked against a C0 signature. Pure Click functions,
predicates, theorems, resources, and logical binders do not have that reason.
Their mixed conventions make it harder to tell which syntax is language-wide
and which syntax is inherited from the attached C declaration.

## Proposed rule

Keep C spelling for verified C function signatures:

```click
int32 vector_get(struct vector* owner, int32 index) {
    // contract
}
```

Use `name: type` for every typed binder introduced by Click itself:

```click
function count(p: int32[], lo: int32, hi: int32) -> int32 {
    // ...
}

predicate sorted(p: int32[], n: int32) {
    forall (k: int32) {
        // ...
    }
}

theorem bounded(x: int32) { ... }
resource buffer(owner: struct buffer*) { ... }
exists (k: int32) { ... }
```

This matches existing theorem parameters, resource parameters, typed `let`
bindings, and witness declarations. Untyped fold/lambda binders such as
`|acc, k|` remain unchanged.

## Scope and non-goals

- Update pure Click function and predicate parameter parsing and printing.
- Update `forall` and `exists` binder parsing and printing.
- Migrate the standard library, examples, mdtests, and documentation.
- Keep the verified C signature grammar unchanged.
- Keep the type vocabulary and pure-function return `-> type` syntax unchanged.
- Do not redesign array-ref types, pointer types, inference, or C-fragment
  syntax as part of this issue.

This is a mechanical consistency change, not a prerequisite for proof tooling.
If migration cost or parser ambiguity turns out to be larger than expected, it
is reasonable to leave this issue open while completing the other language
cleanup.

## Compatibility and diagnostics

Click should retain one canonical spelling rather than accepting both forms
indefinitely. During migration, reject an old Click-native `type name` binder
with a focused message showing `name: type`. Diagnostics for verified C
function signatures must continue to describe their C-shaped parameter syntax
without suggesting the Click-native form.

## Documentation

Document the boundary explicitly:

- a verified C function declaration mirrors C0;
- all other typed binders are Click-native and use `name: type`.

Update the language reference, basic proposition material, pure-function and
predicate chapters, standard-library documentation, and all rendered examples.

## Acceptance criteria

- Pure functions, predicates, theorems, resources, `forall`, and `exists` use
  `name: type` for typed binders.
- Verified C function signatures continue to use and validate C declaration
  spelling.
- Canonical rendering emits only the appropriate spelling for each context.
- Old Click-native `type name` forms receive focused migration errors and are
  not silently retained as aliases.
- The standard library, examples, mdtests, and documentation are fully
  migrated.
- Parser and renderer round-trip tests cover scalar, pointer, array-ref, and
  struct-pointer binder types.
- The default test suite passes.
