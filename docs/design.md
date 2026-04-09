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

* An `eval` function.

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

The reader still produces raw S-expressions. The kernel immediately lowers
those into an internal `Term` language before evaluation. In that internal
term language, bound locals are de Bruijn indices and top-level references stay
as named globals. In the Rust API, `Term` is therefore an opaque type rather
than a public enum, so those lowered local indices do not leak across the
kernel boundary.

Non-atomic surface code forms are tagged lists. For example:

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

Objects are primitive immutable maps from symbol names to canonical terms. The kernel
uses them internally for top-level contexts, and Click code can also build and
inspect them directly with:

```lisp
(object)
(with (object) foo true)
(get obj foo)
(has obj foo)
```

In those object forms, keys are syntax-level symbols, not runtime values.
Those symbols are atomic kernel names, not inspectable strings.

Variables are represented explicitly by name in the surface syntax. Internally,
those names are carried by an atomic `Symbol` type rather than plain strings.

`lambda` binds a scope. Shadowing is allowed. During lowering, the innermost
binder with a given name becomes local index `0`, the next one out becomes
local index `1`, and so on.

Because lowering checks `var` uses against the current local scope and top-level
context, ill-scoped variables are rejected eagerly, including inside lambda
bodies.

The kernel does not have a separate runtime `Value` datatype. Evaluation
produces canonical `Term`s directly. A function value is just a lowered lambda
term in value form. Application evaluates the argument to a canonical term,
substitutes it for local index `0`, and then evaluates the resulting term.

The earlier named-syntax experiments exposed the usual substitution problem:
named binders need alpha-renaming or freshening to avoid accidental capture.
The kernel avoids that by lowering locals to de Bruijn indices before
evaluation.

## Deliberate Omissions

The kernel no longer has `quote`, `car`, `cdr`, `cons`, `atom`, or `atom_eq`.

That is deliberate. The old quote/list path treated code as ordinary list data.
That was convenient for bootstrapping, but it tied code introspection to the
wrong interface. Once binders are represented internally with de Bruijn
indices, exposing code as raw list structure would either leak those indices or
force the kernel to pretend that binders are ordinary tree fields.

So the current kernel does not yet expose first-class code inspection. That is
not because introspection is unimportant. It is because the right interface has
to be binder-aware.

The intended future direction is:

- `Term` is the real kernel syntax.
- raw de Bruijn indices remain an implementation detail.
- host-side construction and inspection of terms should stay binder-safe rather
  than re-exposing lowered locals as ordinary enum variants.
- Click-level introspection over terms should use dedicated, binder-safe term
  operations rather than generic list destructors.

The older quote/list bootstrap experiments are therefore no longer the current
path. They remain useful as historical experiments, but they are not the
present kernel design.
