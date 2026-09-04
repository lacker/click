# Kernel implementation map

This page is for agents modifying Rust implementation, not for users writing
Click specs.

## Core files

- `src/kernel/`: proof terms, C semantics, assumptions, symbolic execution,
  and theorem-producing functions.
- `src/languages/c/syntax.rs`: C0 parser and lowering to kernel C terms.
- `src/surface.rs`: Click parser, validation, lowering, tactics, and proof
  orchestration.

`src/kernel/mod.rs` defines real Rust submodules and re-exports the public
surface from `api.rs` and `primitives.rs`. Cross-module implementation helpers
stay kernel-private with `pub(super)`, and the private `prelude` module keeps
shared imports local to the kernel.

Kernel files:

- `primitives.rs`: core terms, C values/state, propositions, path structs, and
  basic data-type impls.
- `assumptions.rs`: `PureFactContext`, proof obligations, execution-derived pure
  facts (`ExecutionPureFact`), and symbolic execution accessors.
- `api.rs`: public constructors and theorem-producing entry points.
- `reasoning.rs`: deterministic proof helpers, finite forall/range reasoning,
  substitutions, execution-derived pure facts, and obligation plumbing.
- `spec.rs`: `SpecExpression`/`SpecProposition` lowering and evaluation.
- `eval.rs`: C expression/statement evaluation and memory operations.
- `loops.rs`: loop verification, loop effects, loop havoc, and invariant
  helpers.
- `proof/`: persistent checked proof-object infrastructure. Its `branches.rs`
  owns branch and split identities, allocation, and structural topology;
  `storage.rs` owns the shared persistent containers used by proof forks; and
  `execution.rs` owns `ExecutionProofCore`: the C state, typed execution
  frontier, checked execution facts and loop rules, semantic freshness, and
  loop-effect and region state for one proof path. `ProofExecutionState`
  pairs that core with an opaque language presentation record, so the kernel
  can validate terminal frontiers without depending on Surface syntax,
  deferred tactics, expansion cursors, or diagnostic state.
  `obligations.rs` owns the branch-obligation enum, effect selections,
  frontier/proposition/outcome obligations, result-aware outcome state, and
  checked frame authority. Result-aware outcome semantics are paired with an
  opaque Surface presentation just like execution semantics.
  `object.rs` owns the immutable proof-state shape and the opaque
  `ProofObject` handle that keeps one shared state together with its focused
  branch cursor; branch-local state and the open-branch representation live
  with their topology in `branches.rs`.
  Language attachments are opaque parameters and are never interpreted as
  evidence by these modules. Goal-preserving fact/execution successors,
  strict frontier successors, obligation replacement, and conditional
  discharge are kernel state operations. Primitive proposition refinement and
  closing rules are named `ProofObject` operations that return opaque checked
  successors. Proposition case splits and closed-arm joins likewise allocate
  and validate their branch identities inside `ProofObject`; the language
  retains only arm provenance and diagnostics. Logical execution-frontier
  cases reuse that split while sharing the unchanged checked execution core;
  proof-level execution `if` accepts only opaque per-arm presentation and
  clones semantic execution state inside the kernel. Presentation-only
  frontier replacement preserves the kernel core, and loop-invariant closure
  is checked as a named core update. Fresh proof contexts enter through a
  kernel root constructor, and focused-arm bookkeeping can replace only
  non-authoritative fact deltas; generic handle state replacement is confined
  to kernel tests. The raw proof-state fields and handle constructor are
  private to `object.rs`. Checked language drivers publish fixed-state,
  resource, frame, and execution results through focused or frontier-shaped
  operations that preserve unrelated branch topology.
  Completion witnesses and terminal execution-finalization views can be
  constructed only by `ProofObject`.
  `fact_keys.rs` owns structural fact-index keys over kernel propositions, and
  `fact_reasoning.rs` owns the surface-independent equivalence, transport,
  conflict, availability, and explicit universal-instantiation rules used by
  the persistent fact store and proof object.
  `facts.rs` owns that persistent store, its indexes, and its output-sensitive
  ancestry/delta operations.
- `functions.rs`: C function execution, argument binding, and call results.
- `tests.rs`: kernel unit tests.

## Trusted shape

`Theorem` is an abstract object. Callers can inspect its proposition but cannot
construct arbitrary theorems directly. Public functions that return `Theorem`
are trusted theorem-producing operations. In Click terminology these are
axioms, even when Rust names them `prove_*`.

`prove_int32_increment_upper_bound`,
`prove_int32_increment_strictly_increases`,
`prove_int32_increment_lower_bound`,
`prove_int32_increment_greater_equal_lower_bound`,
`prove_int32_increment_strict_greater_lower_bound`,
`prove_int32_increment_preserves_order`, and
`prove_int32_successor_le_implies_lt`, and
`prove_int32_positive_is_nonnegative`, and
`prove_int32_lt_implies_le`,
`prove_int32_not_lt_implies_ge`,
`prove_int32_strictly_positive_is_nonnegative`,
`prove_int32_increment_below_max_is_defined`,
`prove_int32_one_plus_below_max_is_defined`,
`prove_int32_one_plus_strictly_increases`,
`prove_int32_nonnegative_add_within_max_is_defined`,
`prove_int32_nonnegative_subtract_within_value_is_defined`,
`prove_int32_add_nonnegative_right_is_at_least_left`,
`prove_int32_add_nonnegative_left_is_at_least_right`,
`prove_int32_above_one_predecessor_is_at_least_one`,
`prove_int32_positive_predecessor_is_nonnegative`,
`prove_int32_positive_predecessor_strictly_decreases`,
`prove_int32_le_lt_transitive`, `prove_int32_le_transitive`,
`prove_int32_lt_le_transitive`,
`prove_int32_lt_transitive`,
`prove_int32_ge_transitive`, and
`prove_int32_ge_implies_reversed_le`,
`prove_int32_le_implies_reversed_ge`, and
`prove_int32_le_and_not_lt_implies_eq` and
`prove_int32_ge_and_not_gt_implies_eq` are kernel axioms exposed as named standard
theorems. They construct only the fixed signed-increment, checked arithmetic,
predecessor-bound, successor-order, positive-to-nonnegative, and
order-transitivity implications documented in the standard library.
Standard-library verification checks each parsed declaration against its exact
proposition before theorem application becomes available; expanded user proofs
then use the ordinary simple `apply(...) using { ... }` tactic.

Execution theorems retain every verification condition as an implication
premise, including conditions that are not assumable during execution.
`CFunctionExecutionCandidates` is deliberately theorem-free: interpreter- or
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
  execution trace;
- every path verification condition is discharged before any body-safety,
  postcondition, resource, or effect claim is certified;
- all recorded contract claims must have checked evidence for that same exact
  function before `CVerifiedFunctionRule` can be constructed;
- contract instantiation uses simultaneous, capture-avoiding substitution,
  and alpha-equivalence freshens both sides before comparing bound bodies;
- composite-resource fold facts are rechecked against the kernel resource
  state even when a resource body has a guard, so surface lowering cannot
  turn a captured fact into resource authority.

If exact certification cannot reproduce a complete claim set, Click installs
no opaque rule for that function. It does not fall back to a weaker identity
check or to the proof driver's ambient assumptions.

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

When a scalar loop ranking is checked, known pointer-valued branch guards are
not lowered as arithmetic assumptions. The checker still checks the ranking's
nonnegativity and decrease on every such path; omitting an irrelevant pointer
comparison prevents a structural guard such as `node->next != 0` from being
mistaken for an invalid scalar measure. Read-only structural calls inside
ranked loops are therefore supported when the checked surface proof preserves
the observed resource at the loop back edge. Resource-consuming or mutating
transitions across that back edge remain a separate hard-bucket recursion
boundary.

Termination rules live in their own execution-environment map. Constructing or
applying `CVerifiedFunctionRule` does not consult that map, so a termination
feature cannot accidentally turn ordinary `ensures` into total correctness.
The public verification session exposes an explicit query for tools that need
to distinguish the stronger result.

Composite resource unfolding is also checked at this boundary. Resource
definitions carry their logical facts into the kernel, and fold/unfold,
loadability, separation, and post-resource checks are performed against the
exact definition rather than accepted as caller assertions.

Applying a verified function rule lowers the callee's ensures twice when
allocation lifetime effects depend on an outcome: once provisionally to select
the lifetime transition, then against the final memory to publish the public
postconditions. Non-exact loadability needed to state either ensure remains an
explicit certified path obligation. The call rule does not invoke the general
contextual prover to rediscover those range proofs during lowering; their
authority is the already certified callee contract.

When two certified execution paths use different memory snapshots, resource
representation comparison unfolds each composite against its own snapshot.
Unfolding replaces the folded parent with its children while they are
evaluated; keeping both parent and children would create a false ownership
overlap. The composite definition supplies the checked `contains` and
`separate` relations used to compare the resulting child contexts.

## Important types

In `src/kernel/`:

- `Bitvector32Term`: symbolic 32-bit integer terms, including arithmetic,
  `If`, `RangeFold`, and memory loads.
- `PointerOffsetTerm`: pointer-offset expressions.
- `ConditionTerm`: proof-level truth-valued conditions such as signed and
  unsigned order, equality, overflow, and pointer-offset equality.
- `CValue`, `CType`, `Pointer`, `CMemory`, `CState`: C semantic state,
  including the non-object `Void` return value, scalar `int16`, `int32`,
  `uint8`, `uint16`, and `uint32`, pointers, and typed memory loads/stores.
  Kernel execution reports
  `TypeMismatch` if `Void` is used as a condition or object type; it never
  erases that execution path.
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
- `PureFactContext`: known condition/proposition facts plus deterministic reasoning.
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
`int16`, `uint8`, and `uint16` rvalues to `int32` terms for arithmetic, ordered
comparisons, shifts, and bitwise operators, assignments, and returns, adding
internal range facts for the promoted term when an expression needs them.
Scalar `uint32`
addition, subtraction, and multiplication use the same 32-bit term
representation without signed overflow obligations. Unsigned division and
remainder have distinct term nodes so high-bit operands do not inherit signed
division, and unsigned right shift has a distinct logical-shift node. Equality
and ordered comparisons select the unsigned conditions. Stores and function
returns preserve the `uint32` type tag. Scalar narrowing is checked at the
existing boundaries; the coercion adds proof obligations for the target range
unless the current path already proves it. `int16` occupies two bytes with
signed range `-32768..32767`; `uint16` occupies two bytes with range `0..65535`.

## C ABI and memory layout

The C0 importer models one explicit ABI: LP64. In that ABI, `int16` and
`uint16` have size and alignment 2, `int32` has size and alignment 4, `uint8`
has size and alignment 1, `uint32` has size and alignment 4, and every supported pointer
has size and alignment 8. Struct fields are aligned individually and the
struct size includes the tail padding required by its maximum field alignment.
Named enum fields use the supported four-byte `int32` representation. The C0
metadata retains the enum declaration and enumerator values, but lowering
turns an enumerator into its int32 bit pattern and emits the same scalar field
load or store as an `int32` field. The same representation is retained when a
supported struct value is copied by value. Inline scalar-array fields are
copied one element at a time rather than loaded as aggregate `CValue`s.
For example, `{ uint8 buf[16]; int32 a; int32* p; }` places `buf` at byte
offset 0, `a` at byte offset 16, and `p` at byte offset 24, and has size 32.
Inline scalar arrays are retained as aggregate type metadata, but an array
field used in an expression decays to a pointer to its first element; the
kernel never represents the aggregate as a runtime `CValue`. Embedded struct
fields follow the same address-first rule: for `{ uint8 tag; struct inner in;
int32 tail; }` with `inner` sized at 8 bytes, `in` starts at byte offset 4 and
`tail` starts at byte offset 12. The C0 surface carries `in` as an aggregate
place while nested member lowering adds the inner field offset before emitting
the kernel's scalar load or store. Taking the address of a modeled scalar leaf
uses that same typed lvalue path, so the pointer retains the allocation block
and the combined ABI offset rather than materializing an aggregate value.
Direct aggregate loads and copies remain unsupported; resource clauses
currently name nested leaf fields rather than the aggregate itself. Fixed
multidimensional arrays of embedded structs and supported scalar fields retain
their declared shapes in C0 metadata. Indexed leaf access flattens indices in
row-major order before adding the nested struct's complete ABI stride or the
scalar field's element-width stride.
Taking the address of an indexed scalar-array cell uses the same typed lvalue
path, so the resulting pointer retains the containing allocation and points at
the flattened cell rather than at an aggregate temporary.

Copyable by-value structs are the first exception to that address-first
boundary. C0 retains each leaf field name, byte offset, and kernel type in a
flattened `CAggregateLayout`; embedded fields use qualified names such as
`inner.value`. The kernel binds a value to an `AggregateObject` with its own
local block. Parameter binding, local assignment, and aggregate return
materialization allocate fresh blocks and recursively copy the modeled scalar,
array, fixed-dimensional embedded-struct-array leaf, and data-pointer fields.
Multidimensional embedded-struct arrays are expanded in declared row-major
order, so each nested leaf retains its complete element stride. Pointer fields are
shallow copies of typed
eight-byte pointer values: the destination aggregate gets the same pointer
provenance, not a duplicate pointee allocation or ownership transfer. The
aggregate still has no runtime `CValue`: expressions decay to its address for
field loads and stores, while function-pointer fields, unions, and
other unsupported aggregate shapes remain outside this by-value slice.

Field lowering retains these byte offsets as `CExpression::PointerOffsetBytes`;
it must not encode a struct offset by pretending that a struct pointer is an
`int32*`. Tests compare mixed scalar/pointer layouts against Rust `repr(C)` on
the supported LP64 host ABI.

Named unions are represented on the C0 side as address-backed layouts. Every
modeled member has offset zero, and a member read lowers to a kernel typed load
using that member's scalar or pointer type. The kernel still has no runtime
union value or active-member tag; C0 therefore rejects union writes and
whole-union operations, while the tag/member relationship remains an explicit
source-level precondition or branch.

This is not a target-independent C model. Packed structs,
non-LP64 targets, and field types outside the documented C0 subset are not
silently approximated; they must remain unsupported until their ABI rules are
represented explicitly. Bitfields and other compiler-dependent layout rules
are tracked in `issues/multiple-compilers.md`.

Untyped pointer operations likewise do not infer an `int32` pointee. An
untyped load, index, or pointer addition whose pointee type cannot be recovered
produces `CRuntimeError::IndeterminatePointeeType`. Importers should normally
emit typed loads/stores and preserve enough pointer-type information to avoid
that model error.

## Symbolic execution

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
`APPLY_CALL_RULES_AND_VERIFY_LOOPS` for the loop-rule construction phase,
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
owned access. It frees that allocation, clears its cells, consumes those
resources, and rejects surviving direct or composite resource aliases at the
`free` transition. A `views` requirement on an opaque call is a scoped borrow:
call application preserves the caller's original owned or viewed resource but
does not create a new persistent view on return. Thus a borrow from ownership
ends before a following `free`, while any independently present view remains
and must be proved separate or causes `free` to fail locally. Deallocated
identity tombstones make use-after-free and double-free explicit, but carry no
resource authority. `HeapAllocated` and `HeapFreed`
memory derivation DAG edges preserve these transitions for later checking; an allocation
resource that crosses a verified call also determines the allocation delta,
not an untrusted ordinary token. Exact execution records every successful
free as `CHeapAllocationFreed(before, after, base, bytes)`. Effect
certification checks that executing `free(base)` from `before` with the stated
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
definitionally; the subsequent free still needs its independently checked
allocation effect.

If a directly required composite resource has an undecided conditional body,
opaque-contract certification derives both guard cases from the kernel
resource definition and certifies the function in each case from the checked
execution the claim proofs completed. This permits a
proof-only case split to justify branchless C such as unconditional
`free(nullable_pointer)`. Both cases are mandatory; a safe empty/null case
cannot hide an unsafe active-resource case. Mutable footprints inferred from
such a resource retain the same guard. Opaque call application decides that
guard before evaluating the guarded pointer and range, so the empty case does
not manufacture a null footprint while an active malformed footprint still
fails locally.

Certification exposes a derived load through the composites the entry
context holds: it unfolds composites until one holds the cell. That search
asks each unfolding for the cell by structure alone, an exact entry or a
range on the same block whose constant bounds cover it at an equal or
constant-offset base, and unfolds the composite whose pointer argument is the
cell's base first. Only when no unfolding holds the cell by structure does
each unfolding, in the same order, answer with the resource algebra's
reasoning. Reasoning at every unfolding is what once took binary-tree's
certification from seconds to minutes.

A `CallHavoc` edge carries the callee's checked mutable ranges. Load transport
may cross that edge only when the loaded address is proved disjoint from every
range; multiple opaque calls compose by following the corresponding bounded
effect chain. This rule preserves an adjacent unchanged field without exposing
havoc block names in an expanded proof. A dependent address is transported
only when its pointer and index expressions are themselves stable. An
overlapping or undecidable footprint stops the transport.

Loop havoc carries the checked mutable ranges of a whole-loop effect summary
when they are available. Its memory-DAG edge is crossed by the same
range-disjointness rule; a loop with no evaluated footprint remains a barrier.

Independent whole-path checking can regenerate fresh return variables and
`call-havoc` marker identities for the same execution path. Certification
couples those encodings only through matching memory-derivation structure:
local bookkeeping edges are transparent, stores must have equal pointers and
values, and call-havoc edges must have definitionally equal mutable ranges and
matching base histories. An empty store list is not evidence of equal memory.
Fresh return values may be related using kernel-certified path-equivalence facts, but
never by ordinary untrusted facts; exact memory and ghost-resource changes are
still rejected.

## Assumption reasoning

`PureFactContext::proves` is the main deterministic proposition checker. It handles
trivial propositions, condition facts, conjunctions, disjunction cases,
implications, finite forall instantiation, memory access, equality facts, order
facts, and selected memory/frame patterns.

Finite forall instantiation proves `forall k, body` by checking `body` at
every point of a constant box. The box is justified only when the universal
is vacuously true outside it: below the `forall` chain, `body` must be a tree
of `and`, `or`, and nested `forall` nodes whose leaves are all implications,
each leaf's antecedent must bound every quantified variable the leaf
mentions, and the box is the hull of those bounds per variable. A bare
conjunct such as `... and k < 3` disqualifies the body. The trusted
`FiniteForAll` derivation rule recomputes the same box, so a derivation
cannot supply a narrower instance set than the body requires.

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
an opaque-call premise proved during search always has a checked derivation
rather than becoming an assumed verification condition.

Universal introduction treats the quantified variable as a binder, not as an
ambient free variable with the same numeric identifier. Facts containing that
free identifier are shadowed while checking the body, and explicit derivations
apply under the same shadowed context.

When adding proof power, prefer a narrow deterministic rule with a test over a
large heuristic. Good rules usually belong near:

- condition simplification
- bitvector equality
- memory load equality
- finite forall/range reasoning
- frame/effect summary reasoning

## Fold and stdlib reasoning

`Bitvector32Term::RangeFold` is the symbolic representation for pure Click
folds with symbolic bounds. The constructor performs basic simplification:

- equal start/end -> initial value
- one-step range -> substitute once
- small concrete ranges -> unroll

Additional equality logic recognizes count-shaped folds and sum commutativity
for the standard-library `count`/`permutation` proofs.

## Click lowering

`src/surface.rs` has several lowering/evaluation paths because contracts are
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

`SpecElaborationContext` in `src/surface.rs` is the bridge from Surface
Click into Kernel Click. It records scalar spec bindings, Click array refs,
and the memory used for C-fragment reads. The surface's contract environment
carries array refs as `ClickArrayRef { memory, pointer, element_type }`, and
elaboration types indexing by them so `uint8[]` indexing scales by one byte
and returns `uint8`; spec lowering mirrors this with typed `SpecArrayRef`,
typed `SpecExpression::MemoryLoad`, and byte-width
`SpecExpression::PointerOffset`. `old(expr)` derives a new context with
function-entry memory and entry scalar values, then elaborates `expr`
normally. The surface evaluates no expression itself: every C fragment,
wherever it is stated, is elaborated this way and evaluated by the kernel.

Memory access obligations carry the operation byte width. Do not infer load or
store width only from pointer syntax; the operation type is what determines
whether an access needs one byte or four bytes.

When adding a new Click expression or proposition form, search all existing enum
matches for `ContractExpression` and `ClickProposition`. Missing one context
usually causes either a compiler error or an unsupported-feature diagnostic.

## Parser and validation

The Click parser is hand-written in `src/surface.rs`. Validation checks:

- duplicate predicates/functions
- predicate/function arity
- predicate/function namespace conflicts
- unavailable `old(...)`
- unsupported predicate calls in pure `if` conditions
- well-founded recursive Click functions and their `decreases` edges
- explicit nonnegative `int32` induction in pure theorem checking, including
  exact universal instantiation of the local smaller-value hypothesis

Stdlib definitions are parsed and combined with user definitions for validation
and verification.

Pure-function induction deliberately preserves the symbolic evaluation
boundary. The language layer lowers the theorem predicate with recursive pure
applications opaque, constructs a fresh universally quantified strong
hypothesis, and checks every proof branch through the kernel `ProofObject`.
Applying that hypothesis goes through the kernel's exact `forall int32`
instantiation operation: the quantified fact, nonnegative argument, strict
decrease, substituted theorem requirements, and resulting predicate must all
match. The legacy surface checker is presentation-only and cannot publish
theorem authority. The ordinary one-step pure-function elaborator then exposes
the current defining equation; it never uses an unfolding-depth budget. This
machinery is separate from recursive C contract and C-termination judgments.
