# Click Design

This document records the current design direction for `click`.

## Goal

`click` is meant to become:

Click code can prove things about Click code.

You can inspect Click programs, transform them, and prove those transformations correct, all inside Click.

Click aims for complete kernel introspection: the core semantics of the language should themselves be representable, inspectable, and reasoned about inside Click.

## The Kernel

The heart of the Click kernel is a few trusted Rust things.

* A small set of primitive data representations. Right now the important ones
  are lists and named objects. Code and most data stay lispy, but named kernel
  structure like environments fits more naturally as objects.

* An "eval" function. This evaluates code.

* A "typecheck" function. This verifies that a particular thing adheres to a particular type.

* A "declare" function. This processes declarations like `def`, `check`, and
  `theorem`, and extends a context/environment in a pure way.

* A powerful enough typesystem that we can implement proofs via typechecking.

There are perhaps some other details. But this is the idea.

Everything else, we should be able to write on top of the kernel.

## Baby Steps

Once we have the kernel written, we need to do some basic stuff on top of the kernel.

* Implement "eval" and "typecheck" in Click itself.
It's not that we will use these, exactly. But it's a demonstration that the kernel has sufficient power.

* Implement some basic types, typeclasses, type-ish things.
Bool
Nat
Code - a type that represents Click code itself
List<T>
"Total function"
Dependent types, like perhaps Vec<T, n>
Container
Iterator

* Implement some basic proofs
Reversing a list twice gives the same thing
Addition is commutative and associative

## Current Kernel

This is still a prototype kernel.

The current kernel has:

- top-level `def`, `check`, and `theorem` declarations, processed by `declare`
- `quote`
- `object`
- `get`
- `with`
- `has`
- `if`
- `atom`
- `atom_eq`
- `car`
- `cdr`
- `cons`
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
as named globals.

Non-atomic surface code forms are tagged lists. For example:

```lisp
(var x)
(app f a)
(lambda x body)
```

Top-level definitions and assertions are declarations rather than term forms.
The current prototype supports:

```lisp
(def answer 'yes)
(def id (lambda x (var x)))
(check (app (var id) 'a) 'a)
(theorem yes_value 'yes 'yes)
```

`declare` threads a context forward explicitly. It is a pure operation: a
definition evaluates its value in the current context, then returns a new
extended context. In the current untyped prototype, `check` and `theorem`
compare evaluated kernel values for exact equality. `theorem` also binds the
checked value to a name.

Objects are primitive immutable maps from symbol names to values. The kernel
uses them internally for top-level contexts, and Click code can also build and
inspect them directly with:

```lisp
(object)
(with (object) 'foo 'bar)
(get obj 'foo)
(has obj 'foo)
```

Variables are represented explicitly by name in the surface syntax.

`lambda` binds a scope. Shadowing is allowed. During lowering, the innermost
binder with a given name becomes local index `0`, the next one out becomes
local index `1`, and so on.

Because lowering checks `var` uses against the current local scope and top-level
context, ill-scoped variables are rejected eagerly, including inside lambda
bodies.

The kernel evaluator no longer uses closure values. A function value is a
lowered lambda term. Application evaluates the argument, reifies that runtime
value back into a closed term, substitutes it for local index `0`, and then
evaluates the resulting term.

The earlier named-syntax experiments exposed the usual substitution problem:
named binders need alpha-renaming or freshening to avoid accidental capture.
The kernel avoids that by lowering locals to de Bruijn indices before
evaluation.

The bootstrap evaluator for the token core still uses explicit
closure/environment values rather than syntax rewriting. That remains a useful
contrast point: the trusted kernel now uses de Bruijn substitution, while the
self-hosted token-core experiments are still operating on quoted named syntax.

The bootstrap token-core typing story is now split in two: `infer` computes a
term's type, and `typecheck` checks a term against an expected type. The
current conversion rule inside that checker is still modest: it computes types
to weak-head normal form and compares them up to alpha-equivalence, not full
normalization-based definitional equality.

The first proof toolkit now exists on top of that token core: a Leibniz-style
`Eq` proposition, `refl`, and basic equality reasoning terms for transport,
symmetry, and transitivity. So the current state is no longer just "typed
programs"; it already includes basic propositions-as-types and proof terms.

The next proof step is already informative too. A trivial computation lemma
like `if_true` is not yet comfortable in the current system. `Eq` and `refl`
work, but proving that `(if true t f)` equals `t` under an arbitrary predicate
pushes past the current weak-head comparison story. That suggests at least one
more piece is needed before serious proof engineering: either stronger
definitional equality, or a richer checking story than the current
infer-then-compare wrapper.
