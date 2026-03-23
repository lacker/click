# Click Design

This document records the current design direction for `click`.

It is not a frozen spec. It should stay concise, accurate, and focused on the
current actual plan.

## Goal

`click` is meant to become:

- a reasonable language to program in
- a language where programs are easy to inspect and transform as data
- a language where transformations can carry machine-checkable correctness arguments
- a language where meaningful parts of checking and proving infrastructure can be written in the language itself

The long-term vision is not "a theorem prover next to a programming language".
It is one language family that can express:

- programs
- ASTs
- transformations between ASTs
- proofs and checkers about those transformations

## Central Task

The central task of `click` is not "prove arbitrary theorems". It is closer to:

- represent programs as data
- transform those programs
- prove that the transformation preserves the intended meaning

In other words, the language should be good at proving program equivalence and
refinement in the cases that matter.

This should not be overstated:

- arbitrary program equivalence is undecidable
- there will never be a fast complete method for proving equivalence of all programs

The actual target is:

- make many important equivalence proofs easy to express
- make many important correctness claims easy to check
- make proof-producing transformations natural to write

## What Matters In The Core

The most important thing is not that the trusted core be tiny in a line-count
sense. Smallness by itself is not the point.

What matters is that the properties built into the core are simple:

- simple enough to specify clearly
- simple enough to implement correctly
- simple enough to reason about
- simple enough to re-check independently

So the design target is:

- not the smallest possible core
- but a core with simple, explicit judgments

## Layers

The current vocabulary is:

- `P`: the programming core
- `K1`: the small trusted kernel
- `K2`: larger derived checkers, verifiers, and automation

`P` should be a real programming language. It is intended to be Turing-complete.

`K1` does not need to be fast. It does need to be:

- explicit
- predictable
- easy to reimplement
- built from simple judgments

`K2` can be larger, faster, and more ergonomic, as long as it reduces back to
claims that `K1` can check.

There may eventually also be a meaningful distinction between:

- the programming language layer
- the proving/checking layer

But the working assumption is that they should remain one language family with:

- one data model
- one quoting story
- one implementation language

They do not have to be literally identical strata, but they should stay close.

## Preferred First Demo Shape

The first serious demo should not be "build a C compiler".

It should be a small transformation story.

The right shape is:

- a small core language `P1`
- a richer surface or extension language `P2`
- a lowering function `L : P2 -> P1`
- maybe a raising or embedding function `R : P1 -> P2`
- proofs that the transformation behaves correctly

Typical theorems in this shape are:

- lowering preserves meaning
- lowering preserves typing
- `L(R(f)) = f` for `f` in `P1`

That last theorem is especially useful when `R` is an embedding of the core
into a richer surface language.

This is the compiler pattern in miniature:

- represent ASTs
- write transformations on ASTs
- prove the transformations valid

That is the early path toward larger goals like verified compilers, annotated
languages, and proof-producing IR pipelines.

## What The First Proofs Should Look Like

The first useful proof targets are:

- well-formedness of an AST
- typechecking of an AST
- evaluation or normalization of an AST
- a small transformation on that AST
- a checker or proof that the transformation preserves meaning

So the first real milestone should be something like:

1. define a small quoted language
2. define `well_formed`
3. define `typecheck`
4. define `eval`
5. define a transformation
6. prove or check that the transformation preserves behavior

That is a much better first demo than trying to jump directly to full
self-hosting of all of `click`.

## Code As Data

Programs must be representable and inspectable as ordinary tree data.

This is the central Lisp-like constraint. The exact surface syntax can evolve,
but the underlying representation should remain simple and easy to deconstruct.

## Equality And Meaning

The preferred terms are:

- `structural equality`: same tree
- `observational equality`: same behavior under the observations that matter
- `refinement`: one implementation correctly realizes a simpler or more abstract specification

These are the notions that matter for transformation correctness.

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

The current leading `K1` sketch is a quoted token-based core with explicit
binders.

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

The repository currently has three small checker experiments written in
`click`.

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

It does not yet enforce whole-term uniqueness of binder tokens across disjoint
subtrees. It only enforces in-scope uniqueness.

## Open Questions

The main open questions are:

- What is the first small quoted language that should carry a real `eval` / `typecheck` / transformation story?
- Should `K1` require whole-term uniqueness of binder tokens, or only scoped correctness?
- Do we want a canonicalization pass for alpha-insensitive comparison later?
- How close should `P` and `K1` remain once `K1` has explicit `var` / `lambda` / `pi` terms?
- What is the smallest useful typed fragment to self-host next?

## Next Steps

The next repository steps should be:

1. Choose the first small transformation demo.
2. Define the quoted AST for that demo.
3. Define `well_formed`, `typecheck`, and `eval` for it.
4. Define one transformation on that AST.
5. Check or prove that the transformation preserves meaning.
6. Keep `stack` as a programming-core experiment unless it proves useful beyond that.

## Medium-Term Direction

The medium-term goal is to make `click` good at building proof-producing
program tools.

Examples:

- proof-producing analyzers
- proof-producing optimizers
- proof-producing validators for low-level code
- eventually, proof-friendly compiler pipelines

Those tools should themselves be ordinary `click` programs, with soundness tied
back to `K1`.
