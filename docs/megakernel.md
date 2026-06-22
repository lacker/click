# Megakernel Implementation Map

This page is for agents modifying Rust implementation, not for users writing
Click specs.

## Core Files

- `src/megakernel.rs`: proof terms, C semantics, assumptions, symbolic
  execution, and theorem-producing functions.
- `src/lang/c/syntax.rs`: C0 parser and lowering to megakernel C terms.
- `src/lang/click.rs`: Click parser, validation, lowering, tactics, and proof
  orchestration.

## Trusted Shape

`Theorem` is an abstract object. Callers can inspect its proposition but cannot
construct arbitrary theorems directly. Public functions that return `Theorem`
are trusted theorem-producing operations. In Click terminology these are
axioms, even when Rust names them `prove_*`.

## Important Types

In `src/megakernel.rs`:

- `Bitvector32Term`: symbolic 32-bit integer terms, including arithmetic,
  `If`, `RangeFold`, and memory loads.
- `PointerOffsetTerm`: pointer-offset expressions.
- `ConditionTerm`: proof-level truth-valued conditions such as signed order,
  equality, overflow, and pointer-offset equality.
- `CValue`, `Pointer`, `CMemory`, `CState`: C semantic state.
- `CExpression`, `CStatement`, `CFunction`: lowered C0 syntax.
- `CSpecExpression`, `CSpecProposition`: pure specification forms used for
  state-parametric loop invariants. They can embed current-state C expressions,
  fixed-memory loads, pure `if`, `let`, and `RangeFold`.
- `Proposition`: proof propositions, C semantic judgments, memory facts, loop
  invariant rules.
- `Assumptions`: known condition/proposition facts plus deterministic reasoning.
- `ProofObligation`, `PathFact`: obligations and facts produced during symbolic
  execution.
- `Theorem`: abstract proven proposition.

## Symbolic Execution

The symbolic executor produces execution paths. Each path includes:

- public/private path facts
- proof obligations
- outcome theorem

The function-specification prover checks that all paths satisfy the function
contract and that remaining facts/obligations are justified by requirements and
proof machinery.

Budget exhaustion is represented as `ExecutionLimit`. It is a proof/executor
failure, not C undefined behavior.

## Assumption Reasoning

`Assumptions::proves` is the main deterministic proposition checker. It handles
trivial propositions, condition facts, conjunctions, disjunction cases,
implications, finite forall instantiation, memory access, equality facts, order
facts, and selected memory/frame patterns.

When adding proof power, prefer a narrow deterministic rule with a test over a
large heuristic. Good rules usually belong near:

- condition simplification
- bitvector equality
- memory load equality
- finite forall/range reasoning
- frame/effect summary reasoning

## Fold And Stdlib Reasoning

`Bitvector32Term::RangeFold` is the symbolic representation for pure Click
folds with symbolic bounds. The constructor performs basic simplification:

- equal start/end -> initial value
- one-step range -> substitute once
- small concrete ranges -> unroll

Additional equality logic recognizes count-shaped folds and sum commutativity
for the standard-library `count`/`permutation` proofs.

## Click Lowering

`src/lang/click.rs` has several lowering/evaluation paths because contracts are
evaluated in different contexts:

- requirements
- predicate bodies
- postconditions/outcomes
- loop invariants
- old-state expressions

Loop invariants should lower to `CSpecProposition`, not `CProposition`.
`CProposition` is C-expression-shaped; `CSpecProposition` is Click-core-shaped
and is evaluated at the concrete symbolic state where the loop VC needs the
invariant.

When adding a new Click expression or proposition form, search all existing enum
matches for `ContractExpression` and `ClickProposition`. Missing one context
usually causes either a compiler error or an unsupported-feature diagnostic.

## Parser And Validation

The Click parser is hand-written in `src/lang/click.rs`. Validation checks:

- duplicate predicates/functions
- predicate/function arity
- predicate/function namespace conflicts
- unavailable `old(...)`
- unsupported predicate calls in pure `if` conditions
- recursive Click functions

Stdlib definitions are parsed and combined with user definitions for validation
and verification.
