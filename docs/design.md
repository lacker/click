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

* A strong enough type system that proofs can eventually be implemented by
  typechecking.

Everything else should be built on top of that kernel.

## Baby Steps

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

## Current Kernel

This is still a prototype kernel.

The current kernel has:

- top-level `def`, `check`, and `theorem` declarations, processed by `declare`
- `object`
- `get`
- `with`
- `has`
- `if`
- `var`
- `app`
- `lambda`
- `nil`
- `true`
- `false`

Ordinary symbols do not self-evaluate.

The reader parses surface S-expressions, and the kernel lowers them into an
internal `Term` language before evaluation. In that internal language:

- bound locals are de Bruijn indices
- top-level references stay as named `Symbol`s
- `Term` is opaque in Rust, so raw local indices do not leak through the
  public API

The structural kernel API should stay in kernel objects. Public constructors
and evaluators should speak in terms of `Term`, `Symbol`, `Object`, `Context`,
`Declaration`, and `StepResult`, not host closures or raw indices.

Surface term forms are tagged lists. For example:

```lisp
(var x)
(app f a)
(lambda x body)
```

Top-level definitions and assertions are declarations rather than term forms.
The current prototype supports:

```lisp
(def answer true)
(def id (lambda x (var x)))
(check (app (var id) true) true)
(theorem truth true true)
```

`declare` threads a context forward explicitly. It is a pure operation: a
definition evaluates its value in the current context, then returns a new
extended context. In the current untyped prototype, `check` and `theorem`
compare evaluated kernel values for exact equality. `theorem` also binds the
checked value to a name.

Objects are primitive immutable maps from symbol names to canonical terms. The
kernel uses them internally for top-level contexts, and Click code can also
build and inspect them directly with:

```lisp
(object)
(with (object) foo true)
(get obj foo)
(has obj foo)
```

In those object forms, keys are syntax-level symbols, not runtime values.
Those symbols are atomic kernel names, not inspectable strings.

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

The kernel does not have a separate runtime `Value` datatype. The primitive
operational semantics is a single reduction step on `Term`s, and full
evaluation just iterates that step relation until it reaches a canonical term.
A function value is just a lowered lambda term in value form. Application
first reduces its function and argument one step at a time; once both are
values, one beta step substitutes the argument for local index `0`.
Externally, one call to `step` either reports that a term is already a value or
returns exactly one reduct.

`Term` is the real kernel syntax. Raw de Bruijn indices are an implementation
detail.

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
