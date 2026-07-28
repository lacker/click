# Kernel Implementation Map

This page is for agents modifying Rust implementation, not for users writing
Click specs.

## Core Files

- `src/kernel/`: proof terms, C semantics, assumptions, symbolic execution,
  and theorem-producing functions.
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
- `assumptions.rs`: `Assumptions`, proof obligations, execution-derived pure
  facts (`ExecutionPureFact`), and symbolic execution accessors.
- `api.rs`: public constructors and theorem-producing entry points.
- `reasoning.rs`: deterministic proof helpers, finite forall/range reasoning,
  substitutions, execution-derived pure facts, and obligation plumbing.
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

Execution theorems retain every verification condition as an implication
premise, including conditions that are not assumable during execution.
`CFunctionExecutionCandidates` is deliberately theorem-free: replayed or
caller-supplied outcomes are only candidates until a kernel execution
reproduces them.

Opaque function rules have a narrower boundary:

- the rule is bound to the complete `CFunction`, including its lowered body,
  contract, exact claim targets, resource definitions, and execution metadata;
- `CFunctionContractExecution` can only be created by the kernel from the
  exact function's entry state and contract-derived assumptions. Proposed
  elaboration facts are admitted only when the kernel re-derives them from
  that canonical entry, so callers cannot inject hypotheses;
- contract execution mode is explicit. `VerifyLoops` checks annotated loop
  rules, while `ExecuteLoops` independently repeats a bounded concrete
  execution certificate;
- every path verification condition is discharged before any body-safety,
  postcondition, resource, or effect claim is certified;
- all recorded contract claims must have certificates for that same exact
  function before `CVerifiedFunctionRule` can be constructed.

If exact certification cannot reproduce a complete claim set, Click installs
no opaque rule for that function. It does not fall back to a weaker identity
check or to the proof replay's ambient assumptions.

Composite resource unfolding is also checked at this boundary. Resource
definitions carry their logical facts into the kernel, and fold/unfold,
loadability, separation, and post-resource checks are performed against the
exact definition rather than accepted as caller assertions.

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
- `Proposition`: proof propositions, including `ForAll` and `Exists`, C
  semantic judgments, memory facts, and loop invariant rules.
- `Assumptions`: known condition/proposition facts plus deterministic reasoning.
- `ProofObligation`, `ExecutionPureFact`: obligations and facts produced during symbolic
  execution.
- `Theorem`: abstract proven proposition.
- `CFunctionContractExecution`: kernel-produced complete execution evidence
  used only for exact opaque-contract certification.
- `CVerifiedFunctionContractClaim`, `CVerifiedFunctionRule`: unforgeable
  evidence for one exact claim and for a complete exact opaque contract.

The current integer conversion slice is deliberately small. `eval.rs` promotes
`uint8` rvalues to `int32` terms for arithmetic, ordered comparisons, shifts,
and bitwise operators, adding internal byte-range facts for the promoted term.
Stores and function returns use checked `int32`-to-`uint8` narrowing; the
coercion adds proof obligations for `0 <= value <= 255` unless the current path
already proves them.

## Symbolic Execution

The symbolic executor produces execution paths. Each path includes:

- public/private execution-derived pure facts
- proof obligations
- outcome theorem

`prove_symbolic_c_condition_evaluation` is the corresponding direct rule for
C control-flow conditions. It evaluates an expression under assumptions,
applies C truthiness, and returns `CConditionEvaluates` paths for true, false,
undefined-behavior, or runtime-error outcomes. Tactics use this rule to
select `if` edges without constructing a synthetic C statement.

The function-specification prover checks that all paths satisfy the function
contract and that remaining facts/obligations are justified by requirements and
proof machinery.

`prove_c_function_satisfies_specification_from_symbolic_path` accepts only the
exact function, entry state, arguments, and outcome recorded in the certified
path. It does not turn arbitrary outcomes into theorems. The separate
`c_function_execution_candidates_from_outcomes` API constructs no theorem.

Budget exhaustion is represented as `ExecutionLimit`. It is a proof/executor
failure, not C undefined behavior.

Call and loop behavior are explicit inputs to kernel execution. The common
configurations are:

- `CExecutionSemantics::EXECUTE_BODIES` evaluates callee bodies, verifies
  annotated loops directly, and ignores available verified rules. Low-level C
  evaluator tests use this mode.
- `CExecutionSemantics::APPLY_VERIFIED_RULES` applies opaque function and loop
  rules and never evaluates the corresponding bodies. Click execution proofs
  use this mode.

`CExecutionEnvironment` contains the function definitions and verified rules
available to an execution; it does not select between these semantics. In
particular, rule lookup is not a fallback mechanism. Applying verified rules
without a matching rule fails, while direct body verification behaves the same
whether or not a matching rule is present. `CExecutionSemantics` also exposes
`APPLY_CALL_RULES_AND_VERIFY_LOOPS` for the certificate-construction phase,
where calls remain modular while the current loop body is verified directly.

An opaque pointer return is a symbolic pointer block that may alias any
existing block. Only a certified postcondition or resource fact can establish
that it equals an argument or is distinct from existing storage; an opaque
return is not treated as an allocation.

## Assumption Reasoning

`Assumptions::proves` is the main deterministic proposition checker. It handles
trivial propositions, condition facts, conjunctions, disjunction cases,
implications, finite forall instantiation, memory access, equality facts, order
facts, and selected memory/frame patterns.

Universal introduction treats the quantified variable as a binder, not as an
ambient free variable with the same numeric identifier. Facts containing that
free identifier are shadowed while checking the body, and explicit derivations
replay under the same shadowed context.

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
