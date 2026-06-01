# click

`click` is a new programming language.

Click's goal is to make it easy to add proofs to existing programs in other programming languages.

The general idea is to make an extremely flexible kernel and theorem proving system.

English is very flexible. You can cram all sorts of stuff into an English sentence.
Even if it is kind of disgusting. Like sushi burrito hors d'oeuvres.

Click aims to do the same thing, for programming languages.

Click is designed in three layers:

1. A core calculus with computations, values, effects, outcomes, propositions,
   and proofs.
2. An LCF-style logistical layer for naming, scoping, checking, and safely
   reusing definitions and theorems.
3. A structural type system, where a value can belong to many types.

Medium-term goals:
* Keep code quality high. Clean up when things should be cleaned up.
* Make the whole prelude load from `.lisp` files.
* Build out a “standard library” with lots of definitions and proofs about lists.

## Current architecture

The kernel lives in `src/kernel/`:

- `calculus.rs` defines the core calculus entities: `Computation`, `Value`,
  `Effect`, `Outcome`, `Prop`, and `Proof`. `Term` is currently a compatibility
  alias for `Computation`.
- `eval.rs` implements reduction and normalization for computations.
- `check.rs` implements substitution, alpha-equivalence, and the primitive proof
  rules.
- `theory.rs` contains the logistical LCF-style layer: `Theory`, `Theorem`,
  `Context`, and named bindings.

Surface expressions belong outside the core calculus. The prelude source parser
uses S-expressions as input and elaborates them into kernel computations,
propositions, and proofs.

The standard prelude is just a theory built on top of the kernel. It currently
contains the list definitions for `reverse_acc`, `reverse`, and `append`, plus
theorems about those definitions.
