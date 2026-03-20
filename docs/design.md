# Click Design Notes

This document records the current design direction for `click`.

It is not a frozen spec. The point is to keep the principles and the
near-term plan explicit while the language is still changing quickly.

## Goals

`click` is meant to become:

- a reasonable language to program in
- a language where programs are easy to inspect and transform as data
- a language where we can prove theorems about programs written in the language
- a language where large proof automation can itself be written in the language

The long-term vision is not "a theorem prover next to a programming language".
It is one language family with a small trusted core and larger derived layers.

Another way to say the goal:

- `click` should eventually be reflective enough to implement meaningful parts
  of its own checking and proving infrastructure in `click`

That is a better north star than "make the kernel as tiny as possible".

## Layers

There are at least two important layers.

- `K1`: a small trusted kernel for checking proofs / semantics
- `P`: the programming core, which should be expressive enough to write real programs

`P` should be Turing-complete.

`K1` does not need to directly do all programming tasks. It does need to be
small, explicit, and reflective enough to talk about code, proofs, and its own
checking behavior.

Later, larger systems can sit on top of `K1`.

- `K2`: a bigger derived kernel / verifier / automation layer

The intended architecture is:

- trust `K1`
- implement richer tools in `click`
- prove those tools sound using `K1`

This is LCF-shaped: a tiny trusted checker, plus larger untrusted or
less-trusted automation built above it.

### Self-hosting direction

The important medium-term milestone is not merely "have a kernel".

It is:

- write a checker for some useful fragment of `click` in `click`
- use `K1` to state and prove why that checker is sound

So the real balance is:

- enough simplicity that checking is easy to specify and trust
- enough power that the checker can be written in the language itself

This repository should optimize for that balance.

## Design Principles

### One language family

We do not want a hard cultural split between:

- the "real programming language"
- the "theorem language"

Programs, proof search, transformations, and proof checking should all feel
like they live in the same world.

### Code as data

Programs must be representable and inspectable as ordinary tree data.

This is the core Lisp-like requirement. The exact surface syntax can evolve,
but the underlying representation should remain simple, explicit, and easy to
deconstruct.

### Small trusted core

The thing we trust should be very small.

That does not mean the whole language must stay tiny forever. It means:

- the trusted checker should be small
- larger verifiers and tactics should produce certificates or proof objects
- those should be checkable by the small trusted core

The trusted kernel does not need to be fast. It needs to be:

- small
- explicit
- easy to reimplement
- easy to prove richer tools against

Fast checkers can live in derived layers and be proved sound against `K1`.

### Regularity over cleverness

The language should optimize for:

- few special cases
- canonical forms
- explicit semantics
- easy transformation
- easy machine generation

This matters both for proofs and for AI-written code.

### Surface names are optional; semantic names are not fundamental

Variable naming and freshness are a major source of complexity.

The current design direction is:

- user-facing syntax may eventually use names
- the kernel should avoid name-management complexity as much as possible

We do not want "pick a fresh variable" to be a fundamental kernel operation.

The preferred direction is:

- keep human-readable names in the surface language
- avoid making raw names the semantic identity of binders in `K1`

### Strong normalization is not a design goal

The programming core is intended to be a real programming language. It is not
being designed around strong normalization.

## Equality and program meaning

The following distinctions are useful.

- `structural equality`: two values are the same tree
- `observational equality`: two programs behave the same under the observations that matter
- `refinement`: one implementation correctly realizes a simpler or more abstract specification

These names are preferred over more academic terminology when possible.

For example:

- two hash tables may not be structurally equal
- they may still be observationally equal as sets
- one concrete representation may refine an abstract set specification

## Binder and identity direction

Binding remains one of the central open design problems.

Current conclusions:

- raw named binders in the kernel are undesirable, because alpha-equivalence and
  freshness leak everywhere
- de Bruijn-style nameless cores are attractive, but arithmetic/shifting is
  awkward and likely not the simplest path for `K1`
- the current `stack` experiment keeps evaluation small, but probably makes
  theorems about variables and substitution uglier than they need to be

A promising alternative is:

- lower named source terms to a kernel form with unique binder identities
- use those unique identities for equality and environment lookup
- keep freshness generation out of `K1` itself
- optionally canonicalize binder identities later when alpha-insensitive
  comparison is needed

In that world:

- surface names are for humans
- kernel binder identities are for semantics
- runtime environments can stay simple association lists or similar structures

This is still an open area. The main point is to avoid both:

- full name-management bureaucracy in the kernel
- unnecessary arithmetic machinery in the kernel

## Current Programming-Core Direction

The current prototype is experimenting with:

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

### Why `lambda`

Proper lexical closures are required for the programming core to make sense.

Without lexical closures:

- partially applied functions do not behave correctly
- free variables resolve against the wrong environment
- higher-order programming becomes semantically unstable

This is one place where we intentionally move away from classic "Roots of Lisp"
style evaluation.

### Why not `label`

We do not plan to preserve `label` as the recursion mechanism.

It is historically interesting, but it is not the cleanest design for the
programming core. Recursion should come from something cleaner later, such as:

- a fixed-point operator
- a more explicit recursive binding form
- or a similarly simple kernel mechanism

## Lexical Closures

The cleanest known operational story is:

- evaluating `(lambda body)` creates a closure
- a closure contains:
  - the body
  - the lexical environment at definition time
- applying the closure evaluates the body in the captured environment extended
  with the new argument

Conceptually:

```lisp
(lambda body)  ==>  (closure body env)
```

and

```lisp
(apply (closure body env) arg)
  = evaluate body (cons arg env)
```

This avoids:

- substitution-based semantics
- alpha-renaming
- freshness management

The main open design question is how explicit closures should be inside `P`.

### Current prototype

The current prototype now represents closures as explicit list data:

```lisp
(closure body env)
```

This makes the programming core more uniform, but it introduces a new issue:

- programs can fabricate malformed closures as ordinary data

The current rule is simple:

- application recognizes the `closure` shape
- malformed closures are runtime errors / stuck terms

This keeps the evaluator small while preserving list-uniformity.

## The `stack` Experiment

The current prototype exposes the lexical environment through `stack`.

The intended semantics are:

- evaluating `stack` returns the current lexical environment as a list
- the nearest binding is first
- unary `lambda` pushes one value onto that environment at application time

Examples:

```lisp
((lambda stack) 'a)                  ; => (a)
((lambda (car stack)) 'a)            ; => a
(((lambda (lambda (car (cdr stack)))) 'a) 'b)  ; => a
```

This is an experiment.

It is attractive because it makes the evaluator very small and explicit:

- closures capture an environment
- `stack` just returns that environment

It may later turn out that a more canonical variable form is preferable, but
for now we are explicitly exploring the `stack` design.

The current expectation is:

- `stack` may be a useful programming-core experiment
- `stack` is probably not the final binder representation for `K1`

## Short-Term Proof Goals

The short-term target is not "prove everything about lambdas". Lambdas are
infrastructure.

The short-term proof target is:

- get the function/closure story coherent enough
- define ordinary list-processing programs
- prove standard theorems about those programs

Examples:

- `append xs nil = xs`
- `append (append xs ys) zs = append xs (append ys zs)`
- `reverse (reverse xs) = xs`
- `reverse (append xs ys) = append (reverse ys) (reverse xs)`

These are good early goals because they are:

- easy to understand
- strong tests of the proof/program interface
- useful infrastructure for later data-structure and compiler proofs

## Near-Term Repository Priorities

The next repository steps should be guided by the self-hosting checker goal.

Likely next steps:

1. clarify the kernel-facing representation of binders
2. decide whether the current `stack` model remains only an experiment in `P`
3. sketch the first checkable judgment we want `K1` to express
4. write a tiny checker for a very small fragment in ordinary `click`
5. prove simple list-manipulation theorems in that world

The first checker target should probably be very small and structural, not a
full language.

Examples of plausible first targets:

- well-formedness of a tiny lambda/list fragment
- closure-shape validity
- a small typing judgment for a list/lambda subset
- proof objects for basic list equalities

The first implemented experiment in this direction is a tiny closure-shape
checker written in `click` itself.

## Container and abstraction goals

After list proofs, an important near-term theme is proving that different
implementations have the same externally relevant meaning.

Examples:

- a duplicate-free list implementation of sets
- a tree-based implementation of sets
- later, a hash-table-based implementation of sets

The goal is to express and prove things like:

- these two containers have the same contents
- this implementation refines that specification
- these two implementations are observationally equal for set operations

This is important because it is a direct path from small algebraic proofs to
real program reasoning.

## Medium-Term Direction

The medium-term goal is not just "more theorems". It is to show that `click`
is a better language for building proof-producing program tools.

Examples of medium-term directions:

- proof-producing program analyzers
- proof-producing optimizers
- proof-producing validators for low-level code

The important point is that these tools should themselves be ordinary `click`
programs, with soundness checked by a small trusted kernel.

## Working Rule For Now

Until we know better, the working rule is:

- keep the programming core small
- prefer explicit semantics
- accept experiments
- write down principles before they disappear into implementation details

This document should change as the language gets clearer.
