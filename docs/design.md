# Click Design

This document records the current design direction for `click`.

## Goal

`click` is meant to become:

Click code can prove things about Click code.

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

* A `typecheck` function.

* A `declare` function that processes top-level `def`, `check`, and `theorem`
  declarations and extends a context in a pure way.

* A strong enough type system that proofs can be implemented by
  typechecking.

Everything else should be built on top of that kernel.

## Kernel Interface

The Rust kernel interface should be centered on a small set of kernel objects,
and then on operations over those objects. Eventually, the rest of the kernel
should be expressible in terms of this interface rather than ad hoc host-side
helpers.

### Kernel Objects

- `Term`
  The core syntax of the kernel. `Term` is intentionally opaque in Rust.

- `Symbol`
  An atomic name. `Symbol` is used for top-level references, object keys, and
  named variable occurrences before they are lowered under binders.

- `Object`
  An immutable map from `Symbol` to canonical `Term`. The kernel uses `Object`
  internally for top-level environments, and Click code can also construct and
  inspect objects directly.

- `Context`
  An immutable top-level environment of evaluated definitions.

- `Declaration`
  A top-level kernel action. The current variants are `Def`, `Check`, and
  `Theorem`.

- `StepResult`
  The result of a single reduction step. A term is either already a value or
  it reduces to exactly one next term.

### Kernel Operations

- `Term` constructors build kernel syntax directly:
  `nil`, `bool`, `object`, `var`, `lambda`, `if`, `app`, `get`, `with`, `has`

- `Object` provides `new`, `has`, and `get`.

- `Context` provides `new` and `get`.

- `declare(&Context, Declaration) -> ClickResult<Context>`
  applies one top-level declaration and returns the extended context.

- `step(&Context, &Term) -> ClickResult<StepResult>`
  performs one reduction step in a context.

- `run_source(&str) -> ClickResult<Option<Term>>`
  is a convenience entry point that parses surface syntax, processes any
  top-level declarations, and evaluates the final expression.

The core structural interface should stay in kernel objects. It should speak in
terms of `Term`, `Symbol`, `Object`, `Context`, `Declaration`, and
`StepResult`, not host closures or raw indices.

## Semantic Notes

The reader parses surface S-expressions, and the kernel lowers them into an
internal `Term` language before evaluation. In that internal language, bound
locals are de Bruijn indices and top-level references stay as named `Symbol`s.

Variables are represented by `Symbol`. In surface syntax, `(var x)` names a
variable occurrence directly. In the Rust API, `Term::var(Symbol)` does the
same thing. A surrounding `Term::lambda(Symbol, Term)` may capture matching
free occurrences and lower them to hidden local indices; otherwise evaluation
resolves them against the top-level context.

`lambda` binds a scope. Shadowing is allowed. During lowering, the innermost
binder with a given name becomes local index `0`, the next one out becomes
local index `1`, and so on.

Because lowering checks `var` uses against the current local scope and top-level
context, ill-scoped variables are rejected eagerly, including inside lambda
bodies.

The primitive operational semantics is a single reduction step on `Term`s, and
full evaluation iterates that step relation until it reaches a canonical term.
A function value is a lowered lambda term in value form. Application first
reduces its function and argument one step at a time; once both are values, one
beta step substitutes the argument for local index `0`.

`declare` threads a context forward explicitly. It is pure: a definition
evaluates its value in the current context, then returns a new extended
context. In the current untyped prototype, `check` and `theorem` compare
evaluated kernel values for exact equality. `theorem` also binds the checked
value to a name.

## Open Questions

- Click still needs a binder-safe code datatype and term-inspection interface.
  The current Rust `StepResult` is useful for the host kernel, but it is not
  yet a Click-level representation of execution.

- `Term::lambda(Symbol, Term)` is intentionally a smart constructor with
  name-based capture semantics. That keeps the API small and entirely in kernel
  objects, but it is not hygienic across reused subterms. If accidental capture
  becomes a real problem, Click will likely want to split textual `Symbol`s
  from fresh binder identities such as a distinct `Name` type.

- The recursion story is still open. Small-step semantics is the right
  substrate for talking about termination and divergence, but the actual theory
  will depend on whether Click adopts unrestricted recursion, a total core, or
  some explicit fuel or trace discipline.

## Next Steps

Once the kernel is written, the next job is to build enough language on top of
it to test whether the kernel shape is actually right.

* Implement `eval` and `typecheck` in Click itself.
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
