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

`prove_int32_increment_upper_bound`,
`prove_int32_increment_strictly_increases`,
`prove_int32_increment_lower_bound`,
`prove_int32_increment_preserves_order`, and
`prove_int32_successor_le_implies_lt`, and
`prove_int32_positive_is_nonnegative`, and
`prove_int32_positive_predecessor_is_nonnegative`, and
`prove_int32_positive_predecessor_strictly_decreases`,
`prove_int32_le_lt_transitive`, and
`prove_int32_le_and_not_lt_implies_eq` are kernel axioms exposed as named standard
theorems. They construct only the fixed signed-increment, successor-order,
positive-to-nonnegative, and order-transitivity implications documented in
the standard library.
Standard-library verification checks each parsed declaration against its exact
proposition before theorem application becomes available; expanded user proofs
then use the ordinary simple `apply(...) using { ... }` certificate.

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

Recursive C contracts use the standard partial-correctness recursion rule.
While one closed call-graph transaction is being checked, the kernel permits
crate-private provisional rules for the exact functions in that transaction.
Every body is then independently certified with the same safety, effect,
resource, and postcondition checks as an ordinary opaque function. The
language layer returns the completed environment only if every contract
certifies; a failure returns no rules from the transaction. Provisional rules
cannot be constructed through the public kernel API.

The apparently circular rule is justified by finite call depth, not by an
assumption that recursion terminates. Any returning execution has a finite
recursive call tree, so induction on its maximum depth validates each contract
use. An infinite recursive execution owes no return postcondition, while any
undefined behavior or footprint violation still occurs in some finite prefix
and is rejected. Consequently recursive C verification needs no mandatory
decrease annotation and does not create termination evidence.

Optional C termination is a second judgment. Surface `decreases` clauses are
lowered to an untrusted `CFunctionTerminationPlan`; the kernel checks the exact
partially verified function bodies, call-graph components, loop indices,
integer types, guards, and decreasing edges before constructing
`CVerifiedFunctionTerminationRule`. A recursive component is accepted only
when every member has a compatible measure. Whole-function evidence is
withheld if any reachable loop, recursive component, or callee lacks evidence.

For `decreases resource`, the plan contains only an index into the exact entry
resource requirements. The kernel resolves that requirement and the exact
composite definition again, instantiates its guard and direct recursive
children, checks that control flow establishes the active guard before every
recursive edge, and compares every direct self-call's instantiated measure
with a direct child. C-local aliases, logical negation, equivalent comparisons,
scalar truthiness, and branch polarity are normalized from the source body.
The already certified partial contract remains responsible
for the actual resource transfer and memory safety, so a structurally ranked
function may consume or mutate its witness, including freeing a parent after
destroying its child. Thus the surface plan cannot assert ancestry, and an
inactive, unrelated, or same-parent resource does not become decreasing merely
because it has the same resource name.

Termination rules live in their own execution-environment map. Constructing or
applying `CVerifiedFunctionRule` does not consult that map, so a termination
feature cannot accidentally turn ordinary `ensures` into total correctness.
The public verification session exposes an explicit query for tools that need
to distinguish the stronger result.

Composite resource unfolding is also checked at this boundary. Resource
definitions carry their logical facts into the kernel, and fold/unfold,
loadability, separation, and post-resource checks are performed against the
exact definition rather than accepted as caller assertions.

When two certified execution paths use different memory snapshots, resource
representation comparison unfolds each composite against its own snapshot.
Unfolding replaces the folded parent with its children while they are
evaluated; keeping both parent and children would create a false ownership
overlap. The composite definition supplies the checked `contains` and
`separate` relations used to compare the resulting child contexts.

## Important Types

In `src/kernel/`:

- `Bitvector32Term`: symbolic 32-bit integer terms, including arithmetic,
  `If`, `RangeFold`, and memory loads.
- `PointerOffsetTerm`: pointer-offset expressions.
- `ConditionTerm`: proof-level truth-valued conditions such as signed order,
  equality, overflow, and pointer-offset equality.
- `CValue`, `CType`, `Pointer`, `CMemory`, `CState`: C semantic state,
  including the non-object `Void` return value, `int32`, `uint8`, pointers, and
  typed memory loads/stores. Kernel execution reports `TypeMismatch` if `Void`
  is used as a condition or object type; it never erases that execution path.
- `CExpression`, `CStatement`, `CFunction`: lowered C0 syntax. Calls have
  distinct assigned-result and discarded-result statements; a normal
  fallthrough from a `void` body completes with `CValue::Void`.
- `SpecExpression`, `SpecProposition`: Kernel Click forms used for
  state-parametric loop invariants. They can include current-state C fragments,
  fixed-memory loads, pure `if`, `let`, and `RangeFold`. Specification memory
  loads lower deterministically: an exact stored cell reduces to its value;
  otherwise lowering produces a symbolic load term and a loadability
  obligation, rather than selecting an operational alias-resolution path.
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
- `CFunctionTerminationPlan`, `CVerifiedFunctionTerminationRule`: respectively
  an untrusted ranking proposal and separate kernel-checked evidence that the
  exact partially-correct function returns.

The current integer conversion slice is deliberately small. `eval.rs` promotes
`uint8` rvalues to `int32` terms for arithmetic, ordered comparisons, shifts,
and bitwise operators, adding internal byte-range facts for the promoted term.
Stores and function returns use checked `int32`-to-`uint8` narrowing; the
coercion adds proof obligations for `0 <= value <= 255` unless the current path
already proves them.

## C ABI And Memory Layout

The C0 importer models one explicit ABI: LP64. In that ABI, `int32` has size
and alignment 4, `uint8` has size and alignment 1, and every supported pointer
has size and alignment 8. Struct fields are aligned individually and the
struct size includes the tail padding required by its maximum field alignment.
For example, `{ int32 a; int32* p; }` places `a` at byte offset 0 and `p` at
byte offset 8, and has size 16.

Field lowering retains these byte offsets as `CExpression::PointerOffsetBytes`;
it must not encode a struct offset by pretending that a struct pointer is an
`int32*`. Tests compare mixed scalar/pointer layouts against Rust `repr(C)` on
the supported LP64 host ABI.

This is not a target-independent C model. Packed structs, unions, bitfields,
non-LP64 targets, and field types outside the documented C0 subset are not
silently approximated; they must remain unsupported until their ABI rules are
represented explicitly.

Untyped pointer operations likewise do not infer an `int32` pointee. An
untyped load, index, or pointer addition whose pointee type cannot be recovered
produces `CRuntimeError::IndeterminatePointeeType`. Importers should normally
emit typed loads/stores and preserve enough pointer-type information to avoid
that model error.

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

Concrete execution judgments and modular verification transitions are
deliberately different propositions. `CStatementExecutes` and
`CFunctionExecutes` describe outcomes produced by direct operational
execution. `CStatementVerifies` and `CFunctionVerifies` describe abstract
branches admitted while checking partial correctness with loop or function
summaries. A verification return branch means “if this computation returns,
this is an allowed post-state”; it is not evidence that the return is
reachable. Verified contract and loop rules cannot be converted into concrete
execution or termination theorems.

`VerificationDiverges` is an internal outcome marker accepted only inside the
verification propositions. It records a checked path with no finite successor,
so enclosing sequences do not resume and return claims are vacuous. Concrete
execution propositions never contain this marker: divergence has no outcome
in the finite operational relation.

The same distinction governs recursive calls. A recursive contract summarizes
the hypothetical return branch and finite-prefix safety; it never proves that
the call returns. Direct recursion, mutual recursion, and source-order-forward
calls are certified as one closed transaction before any resulting rules are
made available outside it.

An opaque pointer return is a symbolic pointer block that may alias any
existing block. Only a certified postcondition or resource fact can establish
that it equals an argument or is distinct from existing storage; an opaque
return is not treated as an allocation.

Modeled heap allocation is a different kernel transition. A pending symbolic
`malloc` result is refined by ordinary pointer-null control flow or by returning
the result directly. A direct return splits into the same null and success
outcomes; this lets natural allocation wrappers expose a conditional owning
resource without adding a no-op C branch. Registering an unresolved result
records a memory-preserving `HeapAllocationPending` edge, so every preexisting
load remains transportable while the outcome is undecided. Its null arm removes
the metadata and returns to the pre-allocation memory identity. Its success arm
records `HeapAllocated` from the pending snapshot and creates a
fresh heap allocation with an exact, possibly symbolic size, marks its cells
uninitialized, and produces complete owned memory plus the
exclusive `allocation(base, bytes)` lifetime resource. Returning a different
value while an allocation outcome remains unresolved is rejected.

Nonnull `free` requires the exact live base, allocation authority, and complete
owned access. It retires that allocation, clears its cells, consumes those
resources, and rejects surviving direct or composite resource aliases at the
`free` transition. A `views` requirement on an opaque call is a scoped borrow:
call application preserves the caller's original owned or viewed resource but
does not create a new persistent view on return. Thus a borrow from ownership
ends before a following `free`, while any independently present view remains
and must be proved separate or causes `free` to fail locally. Retired identities
make use-after-free and double-free explicit. `HeapAllocated` and `HeapFreed`
memory DAG edges preserve these transitions for replay; an allocation resource
that crosses a verified call is also interpreted as a lifetime effect, not as
an untrusted ordinary token. Exact execution records every successful
retirement as `CHeapLifetimeRetired(before, after, base, bytes)`. Effect
certification checks that replaying `free(base)` from `before` with the stated
extent produces `after`, and chains that transition separately from ordinary
`CMemoryMutatesOnly` and ranged call-havoc effects. This lets a function free
owned storage directly even when its surface `mutable` clause names only
unrelated surviving memory.

Function-effect certification treats stores into heap blocks created after
function entry as internal initialization, not as writes to the caller's
preexisting footprint. Its memory chain may also cross the bookkeeping step
that registers allocation authority for already-owned symbolic storage before
a direct `free`. Both allowances strip only newly introduced trusted heap
state and then require the remaining memory to match the preceding endpoint
definitionally; the subsequent retirement still needs its independently
checked lifetime effect.

If a directly required composite resource has an undecided conditional body,
opaque-contract certification derives both guard cases from the kernel
resource definition and executes the function in each case. This permits a
proof-only case split to justify branchless C such as unconditional
`free(nullable_pointer)`. Both cases are mandatory; a safe empty/null case
cannot hide an unsafe active-resource case. Mutable footprints inferred from
such a resource retain the same guard. Opaque call application decides that
guard before evaluating the guarded pointer and range, so the empty case does
not manufacture a null footprint while an active malformed footprint still
fails locally.

A `CallHavoc` edge carries the callee's checked mutable ranges. Load transport
may cross that edge only when the loaded address is proved disjoint from every
range; multiple opaque calls compose by following the corresponding bounded
effect chain. This rule preserves an adjacent unchanged field without exposing
havoc block names in a surface certificate. A dependent address is transported
only when its pointer and index expressions are themselves stable. An
overlapping or undecidable footprint stops the transport.

Whole-path replay can independently regenerate fresh return variables and
`call-havoc` marker identities for the same execution path. Certification
couples those encodings only through matching memory-derivation structure:
local bookkeeping edges are transparent, stores must have equal pointers and
values, and call-havoc edges must have definitionally equal mutable ranges and
matching base histories. An empty store list is not evidence of equal memory.
Fresh return values may be related using kernel-certified replay facts, but
never by ordinary untrusted facts; exact memory and ghost-resource changes are
still rejected.

## Assumption Reasoning

`Assumptions::proves` is the main deterministic proposition checker. It handles
trivial propositions, condition facts, conjunctions, disjunction cases,
implications, finite forall instantiation, memory access, equality facts, order
facts, and selected memory/frame patterns.

Condition lookup through implication-shaped call facts checks whether the
conclusion can establish the requested condition before proving the
antecedent. Sequential path composition also preserves already-generated
required obligations without rerunning contextual search against the older
base context; final certification remains responsible for discharging that
frontier. These evaluation orders are logically neutral, but prevent ordinary
verified-call chains from repeatedly scanning every earlier call fact.

Smart execution and exact certification share the same bounded order
derivations. In particular, a strict upper bound justifies the non-wrapping
step from `x` to `x + 1` even when the two `x` loads use memory snapshots
connected by deterministic derivation edges. Resource separation also treats
intrinsically distinct pointer blocks as context-free evidence. Consequently,
an opaque-call premise proved during search always has a replayable derivation
rather than becoming an assumed verification condition.

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
- well-founded recursive Click functions and their `decreases` edges
- explicit nonnegative `int32` induction in pure theorem replay, including
  exact universal instantiation of the local smaller-value hypothesis

Stdlib definitions are parsed and combined with user definitions for validation
and verification.

Pure-function induction deliberately preserves the symbolic evaluation
boundary. The language layer lowers the theorem predicate with recursive pure
applications opaque, constructs a fresh universally quantified strong
hypothesis, and replays every proof branch. Applying that hypothesis goes
through the kernel's exact `forall int32` instantiation operation: the
quantified fact, nonnegative argument, strict decrease, substituted theorem
requirements, and resulting predicate must all match. The ordinary one-step
pure-function elaborator then exposes the current defining equation; it never
uses an unfolding-depth budget. This machinery is separate from recursive C
contract and C-termination judgments.
