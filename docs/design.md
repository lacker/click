# Click Design

This document records the current design direction for `click`.

It is not a frozen spec. It should stay concise, accurate, and focused on the
current plan.

## Goal

`click` is meant to become:

- a reasonable language to program in
- a language where programs are easy to inspect and transform as data
- a language where transformations can carry machine-checkable correctness arguments
- a language where meaningful parts of checking and proving infrastructure can be written in the language itself

The long-term vision is one language family that can express:

- programs
- ASTs
- transformations between ASTs
- proofs and checkers about those transformations

## Central Task

The central task of `click` is not "prove arbitrary theorems". It is:

- represent programs as data
- transform those programs
- prove that the transformation preserves the intended meaning

In other words, `click` should be good at program equivalence and refinement in
the cases that matter.

This should not be overstated:

- arbitrary program equivalence is undecidable
- there will never be a fast complete method for proving equivalence of all programs

The real target is:

- make many important equivalence proofs easy to express
- make many important correctness claims easy to check
- make proof-producing transformations natural to write

## Main Vocabulary

The main layers are:

- `kernel`
- `core`
- `surface`
- `tools`

These names are preferred over older overloaded names.

### Kernel

The kernel is the small trusted checker of primitive judgments.

The important design constraint is not raw smallness. The important design
constraint is simplicity of judgment:

- simple enough to specify clearly
- simple enough to implement correctly
- simple enough to reason about
- simple enough to re-check independently

The kernel does not need to be fast. It does need to be explicit and
predictable.

### Core

The core is the explicit language that `click` uses to express:

- recursive functions
- ASTs
- types
- proofs
- transformations

The core should be strong enough to write:

- evaluators
- typecheckers
- proof checkers
- transformation passes

The core is not the same thing as the kernel.

The difference is:

- the kernel checks primitive claims
- the core is the language in which we define interesting programs and claims

In a mature system, the core may be partly checked by the kernel and partly
implemented as ordinary `click` code. They are conceptually different even if
they end up close together.

### Surface

The surface language is the nicer user-facing syntax and convenience layer.

It should lower into the core.

### Tools

Tools are ordinary `click` programs that operate on code.

Examples:

- elaborators
- typecheckers
- simplifiers
- optimizers
- proof search procedures
- compilers

The intended trust story is:

- tools may be large
- tools may be heuristic
- tools may be fast and complicated
- soundness should reduce back to claims the kernel can check

## First Demo Shape

The first serious demo should be a small transformation story.

The right shape is:

- a small core language
- a richer surface or extension language
- a lowering function `L : surface -> core`
- maybe a raising or embedding function `R : core -> surface`
- proofs or checkers showing the transformation is valid

Typical theorems in this shape are:

- lowering preserves meaning
- lowering preserves typing
- `L(R(f)) = f` for `f` already in the core

That last theorem is especially useful when `R` embeds the core into a richer
surface notation.

This is the compiler pattern in miniature:

- represent ASTs
- write transformations on ASTs
- prove the transformations valid

That is the early path toward larger goals like verified compilers, annotated
languages, and proof-producing IR pipelines.

## First Useful Proof Targets

The first useful proof targets are:

- well-formedness of an AST
- typechecking of an AST
- evaluation or normalization of an AST
- a small transformation on that AST
- a checker or proof that the transformation preserves meaning

So the first real milestone should look like:

1. define a small quoted language
2. define `well_formed`
3. define `typecheck`
4. define `eval`
5. define a transformation
6. prove or check that the transformation preserves behavior

That is a better first demo than trying to jump immediately to full
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

These are the notions that matter most for transformation correctness.

## Current Runtime Experiment

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

Malformed closures are allowed as ordinary data, but applying them is an
error.

### `stack`

The current prototype also exposes the lexical environment through `stack`.

Examples:

```lisp
((lambda stack) 'a)                  ; => (a)
((lambda (car stack)) 'a)            ; => a
(((lambda (lambda (car (cdr stack)))) 'a) 'b)  ; => a
```

This keeps the evaluator small, but it is probably not the right binder model
for the kernel-facing language. It makes variables implicit and pushes binder
reasoning into arbitrary `car`/`cdr` code.

Current expectation:

- `stack` is a useful experiment for the runtime and programming side
- `stack` is probably not the final binder representation for the kernel-facing core

## Current Kernel Direction

The leading kernel-facing sketch is a quoted token-based core with explicit
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
- the kernel only sees the tokenized form

This avoids two things we do not want in the kernel:

- full name-management bureaucracy
- de Bruijn arithmetic and shifting machinery

## Kernel v0

There are three different questions that should stay separate.

### 1. Kernel language and judgments

This is the question:

- what terms exist in the kernel-facing language?
- what judgments can the kernel check?

The current `kernel v0` sketch is:

- `type`
- `(var t)`
- `(app f x)`
- `(lambda t domain body)`
- `(pi t domain codomain)`
- some equality form
- some small data story

The likely kernel judgments are:

- context well-formedness
- term has type
- definitional equality / conversion

If proofs are represented as terms, then proof checking is largely a special
case of type checking rather than a separate top-level mechanism.

The exact data story is still open. It could be:

- a very small fixed collection of data types at first
- or a more general inductive-data mechanism

Either way, the kernel needs some way to express ASTs, contexts, proof objects,
and recursive structure over data.

### 2. Trusted Rust implementation

This is the question:

- what Rust code is trusted because it lives outside the language itself?

The trusted Rust part should stay small even if the kernel language itself is
not tiny.

The likely trusted Rust pieces are:

- kernel AST representation
- context checker
- type checker
- normalization / conversion checker
- checking for whatever primitive data/eliminator mechanism the kernel has

The following should ideally stay outside the trusted kernel:

- parser
- surface elaboration
- lowering from richer syntax
- typeclass search
- proof search
- optimization heuristics
- compiler passes

Those can all be ordinary `click` tools that produce terms, certificates, or
proof objects for the kernel to check.

### 3. Primitive rules

This is the question:

- what are the primitive formation, introduction, elimination, and computation rules?

"Axioms" is not quite the right word for most of this. The kernel mostly needs
primitive rules and computation laws.

For `kernel v0`, the likely primitive rules include:

- formation rules for `type`, `pi`, equality, and whatever data mechanism exists
- introduction rules for `lambda` and proof terms
- elimination rules for application and data eliminators
- computation rules such as beta-reduction
- conversion rules for definitional equality

One of the main unresolved questions is how much computation should live inside
definitional equality.

The current bias is:

- structural / obvious computation in the kernel
- bigger recursive programs expressed in the core
- larger proof search and automation outside the kernel

### What probably does not belong in the kernel

At least initially, these are better treated as core, surface, or tool-layer
features rather than kernel primitives:

- typeclasses
- implicit arguments
- fancy syntax
- elaboration
- proof search
- transformation heuristics

Typeclasses are the clearest example here. They may become a very important
part of the core language experience while still elaborating down to simpler
kernel concepts.

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
- Should the kernel require whole-term uniqueness of binder tokens, or only scoped correctness?
- Do we want a canonicalization pass for alpha-insensitive comparison later?
- How close should the runtime language and the kernel-facing core remain?
- What is the smallest useful typed fragment to self-host next?

## Next Steps

The next repository steps should be:

1. Choose the first small transformation demo.
2. Define the quoted AST for that demo.
3. Define `well_formed`, `typecheck`, and `eval` for it.
4. Define one transformation on that AST.
5. Check or prove that the transformation preserves meaning.
6. Keep `stack` as a runtime experiment unless it proves useful beyond that.

## Medium-Term Direction

The medium-term goal is to make `click` good at building proof-producing
program tools.

Examples:

- proof-producing analyzers
- proof-producing optimizers
- proof-producing validators for low-level code
- eventually, proof-friendly compiler pipelines

Those tools should themselves be ordinary `click` programs, with soundness tied
back to the kernel.
