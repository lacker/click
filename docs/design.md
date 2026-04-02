# Click Design

This document records the current design direction for `click`.

## Goal

`click` is meant to become:

- a reasonable language to program in
- a language where programs are easy to inspect and transform as data
- a language where transformations can carry machine-checkable correctness arguments
- a language where the checking and proving infrastructure can be written in the language itself

## The Kernel

The heart of the Click kernel is a few trusted Rust things.

* A "list" representation. This represents code, data, and types. Lispy.

* An "eval" function. This evaluates code.

* A "typecheck" function. This verifies that a particular thing adheres to a particular type.

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

- `quote`
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

Non-atomic code forms are tagged lists. For example:

```lisp
(var x)
(app f a)
(lambda x body)
```

Variables are represented explicitly by name.

`lambda` binds a name. Using a name that is already bound in the current lexical
context is malformed.

The evaluator still uses lexical closures internally, but closures are not part
of Click data.

The bootstrap token-core experiments have already exposed one missing piece:
substitution over uniquely named binders needs an alpha-renaming or freshening
step. Without that, independently closed terms can beta-reduce into malformed
code when binder names collide.

The bootstrap evaluator for the token core now uses explicit
closure/environment values rather than syntax rewriting. The first `Bool`
probe showed that this is the cleaner operational path: it avoids the
alpha-renaming problems that appear quickly in substitution-based evaluation of
named syntax.

The bootstrap token-core typing story is now split in two: `infer` computes a
term's type, and `typecheck` checks a term against an expected type. The
current conversion rule inside that checker is still modest: it computes types
to weak-head normal form and compares them up to alpha-equivalence, not full
normalization-based definitional equality.

The first proof terms now exist on top of that token core: a Leibniz-style
`Eq` proposition and a `refl` proof term. So the current state is no longer
just "typed programs"; it already includes basic propositions-as-types and
proof terms.

The next proof step is already informative too. A trivial computation lemma
like `if_true` is not yet comfortable in the current system. `Eq` and `refl`
work, but proving that `(if true t f)` equals `t` under an arbitrary predicate
pushes past the current weak-head comparison story. That suggests at least one
more piece is needed before serious proof engineering: either stronger
definitional equality, or a richer checking story than the current
infer-then-compare wrapper.
