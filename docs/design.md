# Click Design

This document records the current design direction for `click`.

## Goal

`click` is meant to become:

Click code can prove things about Click code.

The Click kernel should be simple to understand, but powerful enough to self-host.

You can inspect Click programs, transform them, and prove those transformations
correct, all inside Click.

Click aims for complete kernel introspection: the core semantics of the
language should themselves be representable, inspectable, and reasoned about
inside Click.

## The Kernel

The heart of the Click kernel is a few trusted Rust things.

* A small internal term language.

* A public single-step evaluator, plus an internal wrapper that iterates steps
  to a value.

* A `type_of` function.

* A strong enough type system that proofs can be implemented by
  typechecking.

Everything else should be built on top of that kernel. In particular, the
top-level `Context` and `declare` machinery sit above the smallest kernel.

## Kernel Interface

The Rust kernel interface should be centered on a small set of kernel objects,
and then on operations over those objects. Eventually, the rest of the kernel
should be expressible in terms of this interface rather than ad hoc host-side
helpers.

### Kernel Objects

- `Term`
  The core syntax of the kernel. `Term` is intentionally opaque in Rust.

- `Symbol`
  An atomic selector. `Symbol` is used for record fields, sum tags, and surface labels
  that the reader later resolves while lowering.

- `Name`
  An atomic reference to a value binding. Lambda binders, variable occurrences,
  and top-level definitions use `Name`.

- `SymbolMap`
  An immutable map from `Symbol` to canonical `Term`. `SymbolMap` is the shared
  helper used by `record`, `record-type`, `sum-type`, and `match` handlers.

- `NameMap`
  An immutable map from `Name` to `Term`. The evaluator uses a `NameMap` as a
  value assignment, and `type_of` uses a `NameMap` as a type assignment.

- `StepResult`
  The result of a single reduction step. A term is either already a value or
  it reduces to exactly one next term.

### Kernel Operations

- `Term` constructors build kernel syntax directly:
  `type`, `record_type`, `sum_type`, `pi`, `record`, `variant`, `var`,
  `lambda`, `app`, `match`, `get`

- `Term::arrow(A, B)` is the non-dependent convenience constructor for `pi`.

- `SymbolMap` provides `new`, `with`, `has`, and `get`.

- `NameMap` provides `new`, `get`, and `with`.

- `step(&NameMap, &Term) -> ClickResult<StepResult>`
  performs one reduction step relative to a name assignment.

- `type_of(&NameMap, &Term) -> ClickResult<Term>`
  computes the type of a term relative to an explicit assignment of types to
  names.

The smallest kernel should speak in terms of `Term`, `Name`, `Symbol`,
`SymbolMap`, `NameMap`, and `StepResult`, not host closures or raw
Rust strings, integers, or indices.

## Top-Level Interface

This layer is the current Rust foundation: source lowering, context threading,
and declaration processing built on top of the kernel.

- `Context`
  An immutable top-level environment of evaluated definitions. It maps surface
  symbols to canonical names and carries a value `NameMap`.

- `Declaration`
  A top-level action. The current variants are `Def`, `Check`, and `Theorem`.

- `declare(&Context, Declaration) -> ClickResult<Context>`
  applies one top-level declaration and returns the extended context.

- `run_source(&str) -> ClickResult<Option<Term>>`
  is a convenience entry point that parses surface syntax, processes any
  top-level declarations, and evaluates the final expression.

## Semantic Notes

The reader parses surface S-expressions, and the kernel lowers them into an
internal `Term` language before evaluation. In that internal language, variable
occurrences refer to `Name`, not `Symbol`. Surface syntax still spells binders
and references with symbols, but lowering resolves each occurrence to either a
fresh local name or an existing top-level name from the current context.

`lambda` binds a `Name`. Shadowing is allowed because two binders may share the
same display symbol while still being distinct names. During lowering, the
reader allocates a fresh `Name` for each lambda binder and resolves `(var x)`
to the innermost matching binder name, falling back to the top-level context if
needed.

Because lowering resolves all variable references before evaluation, ill-scoped
variables are rejected eagerly, including inside lambda bodies.

The primitive operational semantics is a single reduction step on `Term`s, and
full evaluation iterates that step relation until it reaches a canonical term.
A function value is a lambda term in value form. Application first reduces its
function and argument one step at a time; once both are values, one beta step
substitutes the argument for the bound name.

Products and sums are now explicit in the kernel syntax. `record` values have
`record-type` types. `variant` values have `sum-type` types. Records are still
exact structural products: the type of a record is determined field-by-field.
The empty record now serves as the unit-like value of the kernel, and
`record-type` is its type. There is no separate `Nil` primitive.

Dependent functions are now explicit in the kernel syntax as `pi`. Surface
`(arrow A B)` is only shorthand for a non-dependent function type. The kernel
typing rule for `lambda` synthesizes `pi` when the body type depends on the
binder, and otherwise synthesizes the non-dependent `arrow` abbreviation.

`variant` carries explicit sum structure. That is intentional. In the current
`type_of` design, a bare tagged payload does not determine its full sum type,
so a variant term has to say which `sum-type` it belongs to.

`match` is the elimination form for sums. It first reduces its scrutinee; once
that is a `variant`, it dispatches to the matching handler and turns the step
into an ordinary application. Typing for `match` is exact and structural:
every tag named in the scrutinee's `sum-type` must have a handler, no extra
handlers are allowed, and all handler bodies must synthesize the same result
type. `match` is still non-dependent even though the kernel now has `pi`. In
the surface language, handlers are usually lambdas.

`declare` threads a context forward explicitly. It is pure: a definition
evaluates its value in the current context, then returns a new extended
context. In the current untyped prototype, `check` and `theorem` compare
evaluated kernel values for exact equality. `theorem` also binds the checked
value to a name.

The first typing API is `type_of`. It takes a `NameMap` from `Name` to type and
computes a `Term` type for another `Term`. Lambdas do not carry binder types in
their syntax; instead, the binder's `Name` must already have a type assignment
in the map. `pi` checks its codomain in a type environment extended by its
binder. Application substitutes the argument into a `pi` codomain. This keeps
evaluation Curry-style while still making typing a structural kernel operation.

The current type vocabulary is intentionally small. `pi`,
`(record-type ...)`, and `(sum-type ...)` are ordinary kernel terms, and they
all live in a single `Type` universe. `(arrow A B)` is a surface abbreviation
for the non-dependent `pi` case. This is a prototype typing layer, not yet the
final type theory.

## Open Questions

- Click still needs a binder-safe code datatype and term-inspection interface.
  The current Rust `StepResult` is useful for the host kernel, but it is not
  yet a Click-level representation of execution.

- The current `type_of` judgment is intentionally simple and environment-driven.
  The next design question is whether Click should add bidirectional checking
  on top of it, explicit annotations in terms, or both.

- Click now has dependent functions, but it still does not have dependent
  elimination for data. That means `Pi` exists, but induction does not follow
  from the current `match`.

- The recursion story is still open. Small-step semantics is the right
  substrate for talking about termination and divergence, but the actual theory
  will depend on whether Click adopts unrestricted recursion, a total core, or
  some explicit fuel or trace discipline.

## Next Steps

Once the kernel is written, the next job is to build enough language on top of
it to test whether the kernel shape is actually right.

* Implement `eval` and `type_of` in Click itself.
  This is more of a sufficiency test than a production plan.

* Implement some basic types and type-like structures.
  `Bool`
  `Nat`
  `Code`
  `List<T>`
  total functions
  dependent types like `Vec<T, n>`

* Implement some basic proofs.
  reversing a list twice gives the same thing
  addition is commutative and associative
