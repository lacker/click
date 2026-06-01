# click

`click` is a new programming language.

Click's goal is to make it easy to add proofs to existing programs in other programming languages.

The general idea is to make an extremely flexible kernel and theorem proving system.

English is very flexible. You can cram all sorts of stuff into an English sentence.
Even if it is kind of disgusting. Like sushi burrito hors d'oeuvres.

Click aims to do the same thing, for programming languages.

Click is designed in three layers:

1. A core calculus with computations, values, effects, outcomes, propositions,
   and proofs. Based on a Lisp-like untyped list value.
2. An LCF-style logistical layer for naming, scoping, checking, and safely
   reusing definitions and theorems.
3. A structural type system, where a value can belong to many types.

The medium-term goal is to build out layers 1 and 2.
* Keep code quality high. Clean up when things should be cleaned up.
* Make a prelude that loads from `.lisp` files.
* Build out lots of definitions and proofs about lists, to make sure layers 1 and 2 are well designed.
* Make sure to prove props about props. Like proving strong induction.

It's better to have n simple things, rather than one thing with n different ways to interpret it.
The "many simple things" principle.
So it's okay if the kernel feels like a "pile of different algebraic types".

## Current architecture

The kernel lives in `src/kernel/`:

- `calculus.rs` defines the core calculus entities: `Computation`, `Value`,
  `Effect`, `Outcome`, `Prop`, and `Proof`.
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
