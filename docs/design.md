# Click Design

This document records the current design direction for `click`.

It is not a frozen spec. It should stay short, accurate, and biased toward the
current actual plan rather than old exploration branches.

## Goal

`click` is meant to become:

- a reasonable language to program in
- a language where programs are easy to inspect and transform as data
- a language where programs can be checked and proved correct in the language itself
- a language where proof automation is also written in the language itself

The main near-term milestone is not "the smallest possible kernel". It is:

- write a meaningful checker in `click`
- give that checker a small trusted meaning in `K1`

That is the balance the repository should optimize for:

- enough simplicity that checking is easy to specify and trust
- enough power that the checker can be written in the language itself

## Layers

There are three important layers.

- `P`: the programming core
- `K1`: the small trusted kernel
- `K2`: larger derived checkers, verifiers, and automation

`P` should be a real programming language. It is intended to be Turing-complete.

`K1` does not need to be fast. It does need to be:

- small
- explicit
- easy to reimplement
- easy to reason about

The trust story is:

- trust `K1`
- implement richer tools in ordinary `click`
- prove those tools sound against `K1`

This is LCF-shaped, but the goal is still one language family rather than a
hard social split between "programming language" and "theorem language".

## Principles

### Code as data

Programs must be representable and inspectable as ordinary tree data.

The exact surface syntax can evolve. The underlying representation should stay
simple, explicit, and easy to deconstruct.

### Small trusted core

The thing we trust should be very small. That does not mean the whole language
must stay tiny forever. It means:

- the trusted checker should be small
- larger tactics and verifiers should produce certificates or proof objects
- those should be checkable by `K1`

### Regularity over cleverness

The language should optimize for:

- few special cases
- explicit semantics
- canonical or at least checkable representations
- easy transformation
- easy machine generation

This matters both for proofs and for AI-written code.

### Strong normalization is not a design goal

The programming core is intended to be a real programming language. `click` is
not being designed around strong normalization.

### Surface names are optional; semantic names are not fundamental

Human-readable names may exist in surface syntax. They should not carry the
full semantic burden inside `K1`.

We do not want "pick a fresh variable" to be a fundamental kernel operation.

## Equality and meaning

The preferred terms are:

- `structural equality`: same tree
- `observational equality`: same behavior under the observations that matter
- `refinement`: one implementation correctly realizes a simpler or more abstract specification

These are clearer for `click` than more academic vocabulary when the meaning is
the same.

## Current Programming-Core Experiment

The current runtime prototype is experimenting with:

- `quote`
- `if`
- `atom`
- `atom_eq`
- `car`
- `cdr`
- `cons`
- `lambda`
- `stack`
- `nil`
- `true`
- `false`

Ordinary symbols do not self-evaluate.

### Closures

The current prototype uses proper lexical closures.

Conceptually:

```lisp
(lambda body)  ==>  (closure body env)
```

and application means:

```lisp
(apply (closure body env) arg)
  = evaluate body (cons arg env)
```

In the prototype, closures are explicit list data:

```lisp
(closure body env)
```

Malformed closures are allowed as ordinary data, but applying them is an error.

### `stack`

The current prototype also exposes the lexical environment through `stack`.

Examples:

```lisp
((lambda stack) 'a)                  ; => (a)
((lambda (car stack)) 'a)            ; => a
(((lambda (lambda (car (cdr stack)))) 'a) 'b)  ; => a
```

This keeps the evaluator small, but it is probably not the right binder model
for `K1`. It makes variables implicit and pushes binder reasoning into
arbitrary `car`/`cdr` code.

Current expectation:

- `stack` is a useful experiment for `P`
- `stack` is probably not the final binder representation for `K1`

## Kernel Direction

The leading `K1` sketch is a quoted token-based core with explicit binders.

The basic term forms are:

- `type`
- `(var t)`
- `(app f x)`
- `(lambda t domain body)`
- `(pi t domain codomain)`

Here `t` is a binder token represented as an ordinary atom.

The intended split is:

- surface syntax may use ordinary names
- lowering turns those names into unique binder tokens
- `K1` only sees the tokenized form

This avoids two things we do not want in `K1`:

- full name-management bureaucracy
- de Bruijn arithmetic and shifting machinery

## Current Self-Hosted Checker Experiments

The repository now has three small checker experiments written in `click`.

1. Closure-shape checking
- recognizes runtime values of the form `(closure body env)`

2. Tiny quoted lambda/list well-formedness
- checks a very small quoted fragment built from
  `nil`, `true`, `false`, `stack`, `(quote x)`, `(lambda body)`, and binary application

3. Token-core well-formedness
- checks quoted terms built from `type`, `var`, `app`, `lambda`, and `pi`
- uses an explicit context of in-scope binder tokens

The token-core checker currently establishes:

- `var` tokens must already be in context
- `lambda` and `pi` bind atom tokens and extend the context
- rebinding an already in-scope token is rejected

It does not yet enforce global uniqueness of binder tokens across separate
subtrees. For example, if two disjoint subterms reuse the same binder token,
the current checker may still accept them as long as the token is not already
active in the local context being checked.

That means the current checker enforces in-scope uniqueness, not full
whole-term uniqueness.

## Open Questions

The main open questions are:

- Should `K1` require global uniqueness of binder tokens, or only scoped correctness?
- Do we want a canonicalization pass for alpha-insensitive comparison later?
- How close should `P` and `K1` remain once `K1` has explicit `var` / `lambda` / `pi` terms?
- What is the smallest useful typed fragment to self-host next?

## Next Steps

The next repository steps should be:

1. Define evaluation / normalization for the quoted token core.
2. Define the first typechecking judgment for that same core.
3. Decide what invariants belong in `K1` itself:
   scoped correctness only, or full binder-token uniqueness.
4. Keep `stack` as a programming-core experiment unless it proves useful beyond that.
5. Continue toward small proof objects and basic list/container theorems once the typed core is stable enough.

## Medium-Term Direction

The medium-term goal is not just "more theorems". It is to make `click` a good
language for building proof-producing program tools.

Examples:

- proof-producing analyzers
- proof-producing optimizers
- proof-producing validators for low-level code

Those tools should themselves be ordinary `click` programs, with soundness tied
back to `K1`.
