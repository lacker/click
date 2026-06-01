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

The kernel has a few distinct layers:

- `Term`, `Prop`, and `Proof` are syntax. They represent programs, propositions
  about programs, and proof scripts.
- The kernel checker is the fixed trusted core. It implements evaluation,
  substitution, and the primitive proof rules.
- `Theory` is the growing collection of named definitions and named theorems.
  New terms and theorems are added through `Theory`, which checks them against
  the kernel rules.
- `Theorem` is a checked proposition. Public code can inspect its proposition,
  but does not get to pull out the proof object and treat it as unchecked data.

The standard prelude is just a theory built on top of the kernel. It currently
contains the list definitions for `reverse_acc`, `reverse`, and `append`, plus
theorems about those definitions.
