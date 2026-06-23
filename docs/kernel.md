# Kernel Implementation Map

This page is for agents modifying Rust implementation, not for users writing
Click specs.

## Core Files

- `src/kernel/`: proof terms, C semantics, assumptions, symbolic execution,
  and theorem-producing functions.
- `src/megakernel.rs`: compatibility facade for existing `crate::megakernel`
  callers. New code should use `crate::kernel`.
- `src/lang/c/syntax.rs`: C0 parser and lowering to kernel C terms.
- `src/lang/click.rs`: Click parser, validation, lowering, tactics, and proof
  orchestration.

`src/kernel/mod.rs` defines real Rust submodules and re-exports the public
surface from `api.rs` and `primitives.rs`. Cross-module implementation helpers
stay kernel-private with `pub(super)`, and the private `prelude` module keeps
shared imports local to the kernel.

Kernel files:

- `primitives.rs`: core terms, C values/state, propositions, path structs, and
  basic data-type impls.
- `assumptions.rs`: `Assumptions`, proof obligations, path facts, and symbolic
  execution accessors.
- `api.rs`: public constructors and theorem-producing entry points.
- `reasoning.rs`: deterministic proof helpers, finite forall/range reasoning,
  substitutions, path facts, and obligation plumbing.
- `spec.rs`: `SpecExpression`/`SpecProposition` lowering and evaluation.
- `eval.rs`: C expression/statement evaluation and memory operations.
- `loops.rs`: loop verification, loop effects, loop havoc, and invariant
  helpers.
- `functions.rs`: C function execution, argument binding, and call results.
- `tests.rs`: kernel unit tests.

## Trusted Shape

`Theorem` is an abstract object. Callers can inspect its proposition but cannot
construct arbitrary theorems directly. Public functions that return `Theorem`
are trusted theorem-producing operations. In Click terminology these are
axioms, even when Rust names them `prove_*`.

## Important Types

In `src/kernel/`:

- `Bitvector32Term`: symbolic 32-bit integer terms, including arithmetic,
  `If`, `RangeFold`, and memory loads.
- `PointerOffsetTerm`: pointer-offset expressions.
- `ConditionTerm`: proof-level truth-valued conditions such as signed order,
  equality, overflow, and pointer-offset equality.
- `CValue`, `CType`, `Pointer`, `CMemory`, `CState`: C semantic state,
  including `int32`, `uint8`, pointers, and typed memory loads/stores.
- `CExpression`, `CStatement`, `CFunction`: lowered C0 syntax.
- `SpecExpression`, `SpecProposition`: Kernel Click forms used for
  state-parametric loop invariants. They can include current-state C fragments,
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

Loop invariants lower to `SpecProposition`. This is intentionally Kernel
Click-shaped rather than C-fragment-shaped, so it can carry pure function
bodies such as `.fold` and is evaluated at the concrete symbolic state where
the loop VC needs the invariant.

`SpecElaborationContext` in `src/lang/click.rs` is the current bridge from
Surface Click into Kernel Click. It records scalar spec bindings, Click
array refs, and the memory used for C-fragment reads. Surface contract
evaluation also uses `ClickArrayRef { memory, pointer, element_type }` so
`uint8[]` indexing scales by one byte and returns `uint8`. Loop-invariant spec
lowering mirrors this with typed `SpecArrayRef`, typed `SpecExpression::MemoryLoad`,
and byte-width `SpecExpression::PointerOffset`. In loop invariants, `old(expr)`
derives a new context with function-entry memory and entry scalar values, then
elaborates `expr` normally.

Memory access obligations carry the operation byte width. Do not infer load or
store width only from pointer syntax; the operation type is what determines
whether an access needs one byte or four bytes.

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
