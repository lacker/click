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
- `api/algebraic_cases.rs`: checked constructor exhaustion. For each variant
  of a validated ADT schema it produces an equation to the unchanged
  scrutinee, existentially quantifying that variant's fields. All variants
  occur in the disjunction, and the binders avoid every variable in the
  scrutinee. The justification is the datatype's constructor-generated domain;
  this is a trusted kernel rule, not a smart search result. Its tests check
  typed payloads, malformed schemas, complete coverage, and capture avoidance.
  It does not select a case, introduce free witnesses, or grant resources.
  Entry execution-case elimination shares this schema checker. Its private
  partition reserves the entry function/state, current premises, scrutinee,
  and execution environment before introducing fresh fields. Recording an
  arm checks its exact premise delta and unchanged entry scope. Final path
  certification checks complete coverage of each partition, not merely that
  every retained arm is individually valid. Surface joins a constructor family
  of any width by splitting the frontier over the live arms, and preserves
  lexical bindings across deferred folds.
  An exact contradiction under the partition root plus one constructor
  equation can exclude that arm. The kernel retains the named contradiction
  in a new partition identity, and coverage counts it without a C trace or
  invented return state. Other arms still require checked execution evidence.
  Surface currently accepts an excluded arm consisting of one
  `contradiction(...)`, and splits the remaining live arms normally;
  all-excluded matches remain unsupported.
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
Standard-library verification (`verify_standard_library`, run by the gate)
checks each parsed declaration against its exact proposition. The prelude and
the kernel ship in one executable, so ordinary verifications apply these
declarations as dependencies without re-checking them; expanded user proofs
use the ordinary simple `apply(...) using { ... }` tactic.

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
and is rejected. Consequently the recursive contract rule itself needs no
decrease annotation and creates no termination evidence.

C termination is a second judgment, and the language layer demands it of every
verified function whose signature does not say `diverges`; a marked function
is judged by the contract rule alone. Surface `decreases` clauses are lowered
to an untrusted `CFunctionTerminationPlan`; the kernel checks the exact
partially verified function bodies, loop indices, integer types, guards, and
decreasing edges before constructing `CVerifiedFunctionTerminationRule`. The
two rules stay separate in the environment: applying a
`CVerifiedFunctionRule` never consults termination evidence, so the demand is
a language-layer policy over kernel-checked evidence rather than a change to
what a contract means.

The judgment is local descent. An untrusted planner proposes a height for
every function, the longest path below it in the direct-call graph with the
members of a cycle sharing one height. The kernel never computes call-graph
components or reachability. At each call site it checks that the callee is not
above its caller; a strictly lower callee must already have evidence, and a
callee at the caller's own height is a recursive edge that the declared
function-level measures must rank. Soundness is one induction on the pair of
height and measure, so a wrong height can refuse a function or fail the check
but cannot certify one. Levels are settled in ascending height, which makes
the work linear in the functions and their call edges. A callee outside the
verified set is an assumption in the same sense as its postconditions: an
`extern` contract is trusted to return as its `ensures` is trusted.

A loop owes a measure only when the proof summarized it. Execution summarizes
a loop only when the loop carries annotations: a verified loop rule applies to
a loop with invariant or effect checks, and the invariant route runs for one
with checks or a measure. A loop with none has one route, the concrete one,
which consumes loop budget per iteration and returns only when every feasible
path has left the loop. A function's verified rule exists because
certification executed exactly its body, so the termination check grants such
a loop without a measure, for functions certified on their own and only when
the certified body's loops match the source body's loops shape for shape,
since loop indices name source loops. A linked body with no rule of its own is
not granted this.

A call through a function pointer has no declared callee, and no edge of the
direct-call graph says what it reaches: a function can hand itself to the
helper that calls it, or be stored by one function and called by another that
it calls in turn. The rule is about the address and not the call. Whatever a
pointer call reaches had its address taken, in a body or in a static
initializer, so the check first settles every level with pointer calls
refused; a function certified then returns without going through a function
pointer, in its own body or below, and so can never re-enter a caller through
one. If every address taken names such a function, the levels are settled
again with pointer calls allowed to return. Otherwise the strict verdicts
stand, and the check names each unsuitable callback with the function that
takes its address. A contract-less function whose address is taken is a node
of the graph like an inline helper, because a resolved pointer executes its
body in place. This is a deliberately small rule: a callback that itself
takes callbacks, or a handler table that re-dispatches to lower entries,
terminates for a reason only a measure on the named contract can state, and
that is not built. Each refused
function carries one reason, its own first unranked loop or the first call
not shown to descend, which the surface reports by following refused callees
to the defect that refused them.

An expression `decreases` on a self-recursive function is the one
function-level measure the checker does not analyse a body for. The lowered
component travels on the function's `CFunctionContractInterface`, beside its
`contract_requires`, because the call site is where the descent is owed. At
the entry of the function being certified the kernel reads that component once
and installs a `CRecursionAnchor { function, component, measure: M0,
entry_obligations }` on the `CExecutionEnvironment`; the anchor has no public
constructor, and `c_execution_environment_with_recursion_anchor` reads the
measure off the named function's own interface, so asking for an anchor cannot
choose what it ranks. At a call step whose callee is the anchored function,
`prepare_verified_function_call` reads the same component at the state the
callee's preconditions are read at and emits `0 <= m` and `m < M0`, plus the
viewability the two readings owe, as ordinary verification conditions. A proof
that does not discharge them does not get past the `step()`, and one that
somehow retained them carries them as premises of its path theorem.

The anchor is part of `CExecutionEnvironment`'s identity. Contract
certification derives it itself from the function and arguments in hand rather
than trusting the caller's, and reuses a checked artifact only when
`checked.environment == environment`, so an execution stepped without the
anchor — which raised no descent obligation at its self-calls — is not reused
to certify a contract whose function declares a measure. `checked_function_execution`
refuses such an execution outright as well. What is left for the termination
judgment is that the obligations were reachable and complete: the certified
`CFunction` must carry the measure (the plan names only a spelling, and
`c_verified_function_rule` binds every claim to the same `CFunction`), the
component's only recursive edge must be the self-call, and the function must
not have an inline body. Both are refusals by name; `decreases <int32
parameter>` still ranks those shapes.

A loop is verified as its own judgment and then applied as a summary, so a
self-call inside one is a call no step of the function's own proof takes. The
loop's body is certified under the same anchor instead:
`verify_loop_execution_proofs` asks the kernel for it from the function in
hand, before any loop is planned, so every loop of that function — nested,
inside an `if`, or inside a `switch` — is stepped with it and a self-call in
the body raises the same two members against the same function-entry M0. M0
survives the loop's havoc because it is a closed term over entry symbols and
`collect_execution_environment_variables_uncached` reserves every variable it
names, so no fresh iteration value is handed out on top of one; a measure that
reads memory names the entry memory snapshot, and only an invariant the user
writes relates the iteration's reading to it.

`CVerifiedLoopRule` records the anchor its own body was stepped under. The
kernel writes that field from the environment the paths were produced in and
there is no other way to set it, so it is a record rather than a claim. Two
places read it: `applicable_verified_loop_rule` will not let a rule whose loop
calls the anchored function stand in unless it carries the same anchor —
`checked_function_execution` names that case rather than leaving an
unexplained inapplicable rule — and the termination judgment accepts a
self-call under a loop only when the certified rule for that loop, bound to it
by index and executable shape, carries an anchor for this function and this
declared component. Every loop the call sits inside must carry it, enclosing
as well as innermost, since an enclosing summary swallows the inner one.
Anything else is refused by name.

For a structural `decreases`, the plan contains only an index into the exact entry
resource requirements. The kernel resolves that requirement and the exact
composite definition again, instantiates its guard and direct recursive
children, checks that control flow establishes the active guard before every
recursive edge, and compares every direct self-call's instantiated measure
with a direct child. C-local aliases, logical negation, equivalent comparisons,
scalar truthiness, and branch polarity are normalized from the source body.
A direct child named through a `let` witness is compared semantically instead:
the definition's guard and `where` facts are lowered over a symbolic entry
state with no memory, the call's measure arguments are evaluated there, and
the pure kernel decides the argument equals the witness pointer. Viewability
obligations are assumed, as the syntactic comparison already treats loads as
uninterpreted; every other obligation must be decided.
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

A loop ranking component is not restricted to a C expression. The loop head
carries a `CRankingComponent`: a current-state C expression, a pure
specification expression lowered exactly as a loop invariant's expression is,
or a pure mathematical `Integer` expression lowered exactly as a clause's
Integer operand is. The kernel evaluates that one object at the
iteration-entry state and again at the back-edge state. A pure component
publishes the evaluator's facts
and keeps its reads' viewability obligations, so a measure that reads memory
owes the same viewability the invariant about those cells owes. A component
whose value is not a single value of its carrier at a state, because the state
splits it into
several paths or because a view it reads is gone, is refused rather than
guessed, and a component naming a fixed state is refused at lowering, since a
measure read twice at the same state can never decrease.

The carrier is a function of the component, not of the state, so the two
readings of one component always agree on it. `c_ranking_measure_term` returns
a `CRankingMeasureValue`, `Machine` or `Integer`, and the members are built in
that carrier: `0 <= m` and `m_post < m_pre` are signed int32 comparisons for a
machine component and Integer comparisons for an Integer one. `<` on the
nonnegative Integers is well founded for the same reason `<` on the
nonnegative int32s is, so the termination argument is unchanged; a counting
measure over an array range is naturally an `Integer`, because an int32 fold's
`+` is partial in specifications and its bounds are unprovable at a symbolic
length. A lexicographic tuple may mix the two, because a pivot arm compares
one component's two readings and never two different components; a reading
pair that somehow disagreed on its carrier is refused by name rather than
coerced. An Integer component's address-escape check collects its C locals
from the `FromMachine` and pure-argument positions that can name one, since a
kernel `IntegerTerm` carries no source-level C name.

The plan names a pure component by its declared spelling
(`CRankingMeasureKey::Pure`), which is a weaker match than the structural
equality a C component gets, because the whole-function plan is built before
specification lowering has an environment. The weaker match is not soundness
relevant. Termination evidence is the certified loop's own back-edge bundle,
which discharged `0 <= m` and `m_post < m_pre` for the component the kernel
holds on that rule's loop head; a loop with a nonnegative int32 quantity that
strictly descends on every back edge terminates whichever quantity it was.
The plan only says which loop to point at, and a rule is bound to its source
loop by index and executable shape, a comparison that ignores the measure.
Matching the measures on top of that turns a plan describing one measure and a
certificate carrying another into a named refusal instead of a silent
mismatch, so weakening it can cost a diagnostic and not a theorem. The
address-escape refusal, the one place the plan's measure is read for more than
identification, runs on the certified side for a pure component, where the
lowered expression is available; a lowered form whose C variables cannot be
collected is refused rather than passed unchecked.

Termination rules live in their own execution-environment map. Constructing or
applying `CVerifiedFunctionRule` does not consult that map, so a termination
feature cannot accidentally turn ordinary `ensures` into total correctness.
The public verification session exposes an explicit query for tools that need
to distinguish the stronger result.

Composite resource unfolding is also checked at this boundary. Resource
definitions carry their logical facts into the kernel, and fold/unfold,
viewability, separation, and post-resource checks are performed against the
exact definition rather than accepted as caller assertions.

Applying a verified function rule lowers the callee's ensures twice when
allocation lifetime effects depend on an outcome: once provisionally to select
the lifetime transition, then against the final memory to publish the public
postconditions. Non-exact viewability needed to state either ensure remains an
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
  unsigned order, equality, overflow, pointer-offset equality, and typed
  IEEE floating comparisons/classifications.
- `CValue`, `CType`, `Pointer`, `CMemory`, `CState`: C semantic state,
  including the non-object `Void` return value, scalar `int8`, `int16`, `int32`,
  `uint8`, `uint16`, `uint32`, `int64`, and `uint64`, pointers, and typed
  memory loads/stores.
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
  otherwise lowering produces a symbolic load term and a viewability
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
`int8`, `int16`, `uint8`, and `uint16` rvalues to `int32` terms for arithmetic, ordered
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
unless the current path already proves it. `int8` occupies one byte with
signed range `-128..127`. `int16` occupies two bytes with
signed range `-32768..32767`; `uint16` occupies two bytes with range `0..65535`.
Scalar `int64` and `uint64` retain their signedness through arithmetic,
comparisons, shifts, and bitwise operations; both occupy eight bytes in the
modeled LP64 ABI.

`PureFactContext` reconstructs a conservative signed interval for a term over
the term's own structure, using it to decide overflow and exact equality. A
pure conditional denotes one of its two arms, so its interval is the hull of
the arms' intervals: `if c { 1 } else { 0 }` ranges over `0..1` without the
condition being decided either way. A signed comparison consults that interval
only when one of its sides is a conditional. An ordinary comparison keeps the
indexed order-fact routes and reaches no interval reconstruction, while a
conditional, which no order fact is ever written about, gets the bounds its
arms already state. The hull is a bound, not a case split: a claim that holds
on one arm and fails on the other stays undecided.

## C ABI and memory layout

The C0 importer models one explicit ABI: LP64. In that ABI, `int8` has size and alignment 1, `int16` and
`uint16` have size and alignment 2, `int32` has size and alignment 4, `uint8`
has size and alignment 1, `uint32` has size and alignment 4, `int64` and
`uint64` have size and alignment 8, and every supported pointer has size and
alignment 8. Struct fields are aligned individually and the
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
Direct whole-struct lvalue loads and copies are lowered into typed leaf loads
and stores using the same address-backed layout; the kernel still never
represents a struct as a runtime `CValue`. Resource clauses may name embedded
aggregates directly and expand into typed leaf ranges while preserving their
field metadata. Memory coverage, splitting, and joining are decided bytewise: a
pair is re-spelled into one element width, or compared as byte footprints when
the bounds do not divide. An enclosing owned object can therefore be lent to
satisfy a leaf-width view, and two owners of the same bytes at different widths
are refused as overlapping. Typed loads and stores keep their own widths. Fixed
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
field loads and stores. Union-containing layouts retain a separate typed
overlay for each overlapping member, so aggregate copies preserve all member
views without pretending the members occupy disjoint cells. Adding a union view
forgets raw cells and other-address views that may overlap its bytes, including
those reached through another pointer spelling; a later scalar store similarly
forgets possibly overlapping union views. Views at the union's exact address
remain together when another member is materialized. Direct whole-union
values and member writes remain outside this by-value slice; other unsupported
aggregate shapes remain outside it as well.

Aggregate returns supplied by a pointer-backed whole-object expression have a
small ABI boundary: C0's struct-pointer view is `int32*`, while the internal
address-backed return slot is `uint8*`. The return transition accepts only
those two modeled data-pointer views, retags the address at that boundary, and
copies every modeled leaf into a fresh `__return` block. Consequently a
postcondition such as `result.inner.flag == source.inner.flag` compares the
fresh result cell with the source snapshot without turning the returned
aggregate into an alias or weakening ordinary pointer-return type checks.

Positional initializers for copyable struct-valued locals use the same
address-backed boundary. The C0 parser walks fields in declaration order,
recurses through explicitly braced embedded structs and embedded-struct
arrays, and emits typed stores for each initialized leaf. It emits explicit
zero stores for omitted members and cells, so an automatic aggregate is fully
initialized before later field loads. Designated initializers and struct-array
initializers remain outside this slice; no runtime aggregate value or padding
store is introduced.

Field lowering retains these byte offsets as `CExpression::PointerOffsetBytes`;
it must not encode a struct offset by pretending that a struct pointer is an
`int32*`. Tests compare mixed scalar/pointer layouts against Rust `repr(C)` on
the supported LP64 host ABI.

### Index and offset arithmetic

Two number systems meet in every memory rule, and confusing them is a
soundness bug rather than an imprecision.

Before either of them: **`Bitvector32Term::as_const` answers `u32`, and every
`int32` quantity the kernel orders is a signed number held in those bits.**
An element index, a range endpoint, a block extent, an owned quantity — read
any of them through `as_const` and compare the result, and `-1` becomes the
largest number there is. That single confusion is what `e219bbc8` (range
endpoints), `a98a05e4` (a block extent and a fold quantity) and the commits
beside them each found admitting a false theorem.

So a rule that wants a *number* asks `signed_bitvector_constant`, which is the
one blessed reader for the signed value of a constant `int32` term, or
`exact_signed_constant` where a recorded exact equality may name that value
instead — it is `signed_bitvector_constant` plus one hop through the condition
facts, and nothing else may be asked in its place.
`concrete_memory_range_bounds` is the reader for a whole constant range: it
composes both endpoints and the base offset into signed byte bounds, and a
rule comparing two constant ranges should ask it rather than scale endpoints
itself. `nonnegative_int32_value` is a different question with a similar
shape — the signed value of a raw word *when it is nonnegative*, which answers
`None` rather than a negative number, and exists for the bound rules that want
a positive constant addend.

A **population count** is a third number, and reading it as either of the
other two is the same class of bug. It is a mathematical natural number,
carried in an `int32` term because that is what a contract writes, so a total
of two quantities is either that total or it is nothing.
`population_quantity_sum` forms one only where it is **exact**, and reads
exactness off the two terms alone: two constants whose signed sum stays inside
`0..=i32::MAX`, which is the range a count may occupy at all, or a merge that
undoes a split, where `used + (available - used)` is `available` whatever the
pieces are. Two symbolic quantities are not a total — they carry no relation
the terms show — while a symbolic quantity absorbing a *constant* addend
still is, which is the documented remaining gap rather than a claim of
exactness: `count + 1` overflows at `i32::MAX` like anything else, it is the
merge every refcount contract is written with, and the ledger's own
accumulation across a call is unguarded beside it, so withdrawing it here
would close nothing. Adding two quantities with the modular `Bitvector32Term::add`
instead made two `produces 2000000000 of tok(o)` clauses a population of
`-294967296`, and every quantity rule beneath reads a quantity as signed, so
`ensures count(tok(o)) < 0` verified over four billion produced units.

It consults no facts, deliberately. A merged quantity travels inside a
resource fact, and a contract is certified against a recomputation holding a
different context, so a rule that merged under one context and declined under
the other would make generation and check disagree about a number — which
reaches the user as a completion mismatch rather than as a refusal naming the
quantity. The place the no-overflow condition is *owed* instead of decided is
`count(...)`'s own pattern sum in `src/kernel/spec.rs`: it has an obligation
list to put `not signed_add_overflows` on, the same condition C's `+` owes,
and a contract discharges it there.

`None` from that reader is not a smaller count. Each caller says what an
unformed total costs, and none of them substitutes one: a merge declines to
merge and leaves both facts in the state, a contract's counted-population
transition refuses and names the population, a published `count >= visible`
relation is left unpublished, and the wildcard pattern's ledger fold answers
that it has no sum.

`as_const` itself stays right for the questions that really are about bits:
equality, a map or hash key that carries no order, and the width-scaling
arithmetic that is modular by definition. A key that *is* ordered — the
`concrete_memory` index, whose predecessor and successor probes stand in for a
pairwise scan — is an ordering question wearing a key's clothes, and takes the
signed reading.

A **byte offset** is mathematical. `PointerOffsetTerm` adds exactly, and
`PointerOffsetTerm::scale_int32` sign-extends its index before multiplying by
the element width, so a pointer's displacement from its block is an `i64` that
never wraps. An **element index** is modular. `Bitvector32Term` is a 32-bit
machine value, so `Bitvector32Term::add` and `Bitvector32Term::subtract` wrap:
`i + 1` is the successor of `i` only while that add does not carry out, and at
`i == i32::MAX` it is `i32::MIN`.

The two meet in `element_index_from_offset`, which divides a byte offset by an
element width and folds the pieces with the *modular* add. What it returns is
therefore the element delta only **modulo `2^32`**, and the same is true of
`Pointer::element_index_from_base_with_width` and of every endpoint a rule
builds with `Bitvector32Term::add(base_index, range.start())`. So is
`affine_bitvector_difference_constant`, which walks two index terms as affine
forms in `i64`: the constant it returns is the true difference modulo `2^32`,
no more.

A residue is enough for a **disequality** — nonzero modulo `2^32` is nonzero —
and enough for an **exclusion**: an index whose residue from a range's start
reaches the range's element count is outside the range whichever way the terms
wrapped, which is what `bitvector_index_outside_range_shallow` uses, against
the count bound `affine_range_element_count_bound` supplies.

A residue is **not** enough for **membership**, in either its pointer form
("this cell is inside that range") or its containment form ("this range is
inside that one"). The wrapped reading of a residue `r` is `r - 2^32`, which is
*outside*, so a positive conclusion has to rule it out. That is
`exact_affine_index_difference`, which answers only for a residue it can show
is the difference, and `Pointer::exact_element_delta_from_base`, which keeps
the exact `i64` constant part of a delta beside its one symbolic index rather
than folding them with an add that wraps.

What a range denotes follows the same split. `p[start..end)` is
`memory_range_byte_count` bytes from the *address* of element `start`, so its
element count is the **signed value of the 32-bit term `end - start`** — the
residue, read as `int32`, which `affine_range_element_count` returns. A range
is therefore not "the elements from `start` to `end`": `p[i32::MAX..i32::MIN]`
is a forward range of exactly one element. A rule that compares one range's
`end` against another's, rather than comparing counts, is reading `end` as
`start + count` and owes that the forward half of the valid-extent condition,
`0 <= end - start`.

The valid-byte-extent condition itself is `memory_range_element_count_guards`,
and it is the one definition: `0 <= count` plus, where the element width
constrains an `int32` count at all, `count <= u32::MAX / width`. A stated
`owns` or `views` range brings it, through
`stated_loadable_extent_guards`. A range the kernel synthesizes — a loop
`modifies` frame, a havoc-derived range — does not, so a rule that needs it
must ask rather than assume.

A range named by a stated `separate(memory(…), …)` sits between the two.
`stated_separation_extent_guards` is the separation family's counterpart of
`stated_loadable_extent_guards`: the ranges a separation names are read back by
the same element arithmetic as an owned range, so wherever a separation is
assumed its ranges' guards are available with it. What a separation does *not*
do is owe an undecided guard as a proof obligation. A range reached through a
composite clause — `views readable_input(data, length)`, whose inner
`views data[0..length]` states the extent inside the resource body — publishes
no guard to the code that names the range, so such an obligation would be one
no contract text could discharge. A stated separation is therefore refused only
where the surrounding facts already *decide* that one of its ranges runs
backwards, which is what `separation_extent_is_impossible` asks and what keeps
`separate(memory(a[s..t]), …)` from being written with `s == i32::MAX` and
`t == -i32::MAX`. The undecided wrapping case, `separate(memory(a[s..s + 2]),
…)` for an unconstrained `s`, is still accepted; surfacing a composite's inner
range guards to its user is what would let it be owed.

## Floating-point semantic boundary

The kernel models `float` and `double` as typed IEEE-754 payloads in `CType`
and `CValue`. Slices 1 through 5 carry those payloads through parameters, locals,
structs, arrays, allocation, typed memory loads/stores, and copies at their
declared widths. Constant casts use integer-space round-to-nearest,
ties-to-even conversion, and unary negation is a sign-bit operation. Same-width
comparisons and classification predicates use typed conditions: symbolic values
split paths without being coerced to ordered mathematical reals. Floating
arithmetic uses typed `Float32`/`Float64` operation terms. Constant operations
are evaluated by an integer-space IEEE-754 evaluator; symbolic operations remain
opaque until their operands become constant. The source expander still rejects
floating-point environment directives.

The C model is deliberately fixed to the supported LP64 ABI: `float` is
IEEE-754 binary32 with size and alignment 4, and `double` is IEEE-754 binary64
with size and alignment 8. `long double`, decimal floating point, compiler
extended precision, alternate rounding modes, `fenv` access, and traps are
outside the model. Each operation is evaluated at its declared result type
using round-to-nearest, ties-to-even; the host's floating-point mode and any
excess precision must not affect a certificate.

Floating-point terms and values retain enough representation to
distinguish finite values, signed zero, infinities, and NaNs. Copying a value
preserves its representation, while generated NaNs use one documented
canonical representation. Arithmetic and comparisons follow the C/IEEE rules:
signed zeros
compare equal, every ordered comparison with a NaN is false, and `!=` with a
NaN is true. IEEE overflow and floating division by zero produce infinity or
NaN results; those are not integer-style C undefined behavior. Converting to an
integer is a separate checked operation and is undefined for NaN, infinity, or
an out-of-range value. Classification predicates and raw representation casts
are separate modeled interfaces, not permissions to inspect or reinterpret
kernel internals. Classification is exposed through the source-level
`isfinite`, `isinf`, `iszero`, `issubnormal`, and `isnan` builtins. Constant
classification folds by IEEE bit rules; symbolic classification remains a
checked condition suitable for path assumptions and contracts. Constant
float-to-integer conversion is accepted only for finite, representable values;
other float-to-integer casts remain explicit unsupported/type-error outcomes
when their definedness checks are not established; symbolic conversions carry
those checks as proof obligations.

Unsupported floating-point syntax must remain an actionable, source-positioned
frontend diagnostic. Slice 1 accepts decimal literals only as typed payloads;
hexadecimal literals and unsupported suffixes remain rejected. The evaluator
does not delegate symbolic semantics to host `f32` or `f64`; the operation term,
integer-space evaluator, and certificate checker agree on the exact width,
rounding, exceptional values, and conversion rules. Symbolic float-to-integer
conversions retain finite and range obligations at function, assignment, and
return boundaries.

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

One symbolic execution has exactly one fresh-identity counter, and it lives on
that execution's `ExecutionBudget`. A loop head's havoc of modified locals, a
re-bound binder's model fields, an opaque call result, a heap allocation, an
aggregate field, and a branch join's abstraction all draw from it, so two of
them cannot hand the same identity to two different things. Reserved-set
probing narrows what an individual stream will issue; it is not the mechanism
that keeps allocators apart, because several allocators do not probe at all.

A rule that abstracts a state therefore both takes the counter and reports
where it left it. `abstract_c_state_for_join` and its siblings take the
maximum of the arms' counters — the arms' abstractions are compared for
equality, so they must count from one shared lower bound — and return a
`CStateJoinAbstraction` carrying the state beside the mark the joined
execution continues from. Returning the pair is deliberate: a caller cannot
take the abstract state and keep the old counter. A loop head's
`CLoopPreservationContext` reports its mark the same way, and both the
iteration that continues past the loop and the body proof that runs inside it
start from that mark rather than at the base of the range.

**Within one execution the counter only moves forward, and only the kernel
moves it.** `ExecutionProofCore::next_kernel_variable` is private: a caller
reads it with `kernel_variable_mark` and can only change it through
`advance_kernel_variable_mark`, which refuses a mark below the current one. A
rewound counter re-issues identities that a loop havoc, a join abstraction, a
heap block, an opaque call result or a resource model field is still using,
which is a false-theorem hazard rather than merely wasted identities. Where a
step's evaluation advances the counter, the surface reads a copy, runs the
evaluation, and installs the result through that setter; where a join invents
identities, the kernel installs the mark of the abstraction it recomputed
itself (`ExecutionProofCore::record_interface_branch_join`), so a surface-
chosen successor counter cannot survive the check.

**A budget is either the start of an execution or a continuation of one;
there is no default.** `ExecutionBudget` has no `Default` outside tests, and
no constructor that supplies a fresh-identity counter to a caller who wrote
nothing. Every construction says which it is:
`ExecutionBudget::for_new_execution` starts the counter at
`KERNEL_VARIABLE_BASE` and is legitimate only where no live state carries
identities some execution issued — a symbolic execution over a state the
caller built, a whole-function contract certification, a refinement context
invented from two contract interfaces. `ExecutionBudget::continuing_from`
takes the mark an execution has already reached and counts up from there.
The work allowances of a selected expression, statement or function are
builder steps (`with_c_expression_cost` and its siblings) added to whichever
of the two the call site opened, so the choice stays visible there rather
than hiding inside a constructor. Restarting the counter by writing nothing
was how a loop-havocked local and a re-bound model field, and a
join-abstracted pointer and a later heap block, became one `Variable`.

`ExecutionBudget::beside_live_state` is the third constructor, and **it
cannot invent an execution identity at all** — it may still mint match
binders, which come from their own reserved range. Its users are the
proof-side evaluation families reached from the surface's `have`, `fold`,
`unfold` and theorem-application drivers — the fixed-state spec lowering and
capture entry points, the composite-resource proposition evaluators, the
instance fold/unfold rewrites, the arm-premise and witness binders, the loop
invariant and effect obligation APIs, and independent contract certification.
Those drivers do not carry the execution's mark, so a counter started at the
base of the range would name what the live state already holds: a havocked
local, a join abstraction, a heap block. `allocate_kernel_variable` refuses
with `ExecutionLimit::ExecutionIdentityBesideLiveState` — "internal: execution
identity requested beside a live state" — rather than restarting silently.
Fifty-one named-hazard sites become enforced cannot-allocate sites without
threading anything through the proof engine; a site that genuinely needs an
execution identity has to be given the mark and use `continuing_from`.

This is enforceable because the one site that did allocate no longer needs to.
`c_lower_spec_proposition_with_checked_obligations`, the lowering every
proof-side proposition and contract clause shares, handed out the first
identities of the range as match-arm binders — one per constructor field of a
`match` whose scrutinee is not a literal. Those binders are *bound* variables
of the lowered term, and a bound variable that equals a live free identity is
only harmless while every rewrite that eliminates a binder renames on capture.
`rewrite_integer_match_typed_fields` does not see the binding at all: it is
handed the arm body alone, lifted out of its `Match`, where a bound occurrence
of the binder and a free occurrence of a loop-havocked local with the same
identity are the same syntax. It substituted both, so `have match Box::Wrap(m)
{ Box::Wrap(h) => to_integer(i) } == to_integer(m)` proved `i == m` for the
loop's arbitrary `i` (`mdtests/match_binder_captures_havocked_local.md`).

Binders now come from `ExecutionBudget::MATCH_BINDER_VARIABLE_BASE` through a
counter the budget owns, so nested matches within one lowering get distinct
binders and no binder can equal a free identity of any execution. Two
separately lowered terms do reuse binder identities, because each budget
starts that counter at the base; that is safe because they are bound.
Substituting one such term under the other's binder goes through `TermRewrite`,
which alpha-renames a binder that would capture a free variable of the
replacement and stops substituting under a binder that shadows the variable
being replaced, and alpha-equivalent terms are interchangeable. A shared
*free* identity is not, which is why the case witnesses of
`algebraic_case_paths` — free variables of the constructor equation they
publish, not binders — still come from the execution counter and therefore
refuse beside a live state. `rewrite_integer_match_typed_fields` also checks
what it is given: every identity it substitutes must satisfy
`ExecutionBudget::is_match_binder_variable`, which is what makes the
substitution capture-correct on its own terms rather than by trusting its
caller.

The mark is execution-relative — an offset from `KERNEL_VARIABLE_BASE`, which
is the representation `ExecutionBudget::continuing_from` takes and
`ExecutionBudget::next_kernel_variable` returns. A freshness probe that
compares a candidate `Variable` against it must add the base back:
`ExecutionProofCore::issued_kernel_variable_bound` closes the range
`KERNEL_VARIABLE_BASE .. bound` holding everything this execution has issued.

The counter's range is bounded at both ends. It starts at
`ExecutionBudget::KERNEL_VARIABLE_BASE` and refuses at
`ExecutionBudget::KERNEL_VARIABLE_CEILING`, which is the lowest identity a
producer outside the execution reserves by a constant base. Those producers
pick identities by a constant and a hash and so cannot avoid an execution that
has counted into their range; the execution refuses with
`ExecutionLimit::KernelVariables` instead, which is one comparison per
allocation. The reserved ranges are:

| Range | Producer |
| --- | --- |
| `1_000_000 .. 2_000_000` | the execution's fresh-identity counter |
| `2_000_000 ..` | the surface's quantifier variables |
| `3_000_000 .. 1_003_000_000` | the spec fold binders (`spec_fold_bound_variable`, base plus hash) |
| `4_000_000` by `65_536` | the surface's algebraic binders (`ALGEBRAIC_VARIABLE_BASE`) |
| `4_000_000_000 .. 8_000_000_000` | symbolic pointer blocks |
| `1 << 40 .. 1 << 41` | load variables (`LOAD_VARIABLE_BASE`) |
| `1 << 41 .. 1 << 42` | match-arm binders (`MATCH_BINDER_VARIABLE_BASE`) |
| `1 << 42 .. 1 << 43` | universal-introduction witnesses (`UNIVERSAL_WITNESS_VARIABLE_BASE`) |

The match-binder range is the one that carries a soundness obligation rather
than a hygiene one, so `the_match_binder_range_is_disjoint_from_every_other_producer`
asserts the disjointness instead of leaving it to this table. A lowering that
exhausts it refuses with `ExecutionLimit::MatchBinderVariables`.

The witness range carries the same kind of obligation. `intro` on
`forall v. body` replaces `v` by a free identity standing for an arbitrary
value, so it must name nothing the surrounding state names — and the facts are
not the whole of that state, since a C proof also carries program variables, a
symbolic store, a memory snapshot and a resource context. Choosing the witness by
scanning up from `Variable(0)` for an identity no fact mentions therefore
started in the C identity range and could land on a live program variable;
`the_universal_witness_range_is_disjoint_from_every_other_producer` and
`a_freshened_universal_witness_never_takes_a_c_identity` assert the range
instead. A proof that exhausts it refuses rather than reusing an identity.

Freshening a binder is a renaming, so it must not change what the proposition
says *or how it is spelled*: a proof state matches a goal against a fact
syntactically, and a goal that quietly moves to another canonical form stops
matching the surface's re-lowering of the same written range. That is why a
range's byte extent has exactly one constructor — `memory_range_byte_count`
folds through `Bitvector32Term::subtract`, the same one substitution rebuilds
terms with — rather than a private near-copy that cancels a little less.

### Automatic object identity

A `local:` block is an automatic object's identity, and around seventy kernel
sites read two equal blocks as one object: the same extent, the same cells, the
same answer from every distinctness rule. Each execution of a declaration must
therefore get a block no other automatic object in that memory has, live or
ended.

Three spellings reach a `local:` block. `local:<name>` is the plain one;
`local:lifetime:<n>:<name>` is a generation, taken from the `next_local_lifetime`
counter the state threads through calls and returns; `local:frame:<n>:<name>` is
a call frame's slot for an addressable or aggregate parameter. All three keep
the `local:` prefix, so every rule that asks whether a block is a local still
gets the same answer, and the diagnostic renderer spells all three by the last
segment — the name the reader wrote.

`local_declaration_pointer` is the only place an automatic object's identity is
created, and it is where the uniqueness is established rather than assumed. It
takes a generation when any of three things is true:

- this frame is re-entering the declaration — a loop, or an inner scope
  shadowing the name — which the locals map sees, and whose old object's
  lifetime ends first;
- the memory already holds or has retired a block of that spelling; or
- a frame this one was called from holds bindings at all. A called frame
  executes on the caller's memory with its own locals map, so it cannot see the
  caller's objects, and an object the caller holds only as a value — a parameter
  whose address it never takes — has no block in memory to find. A frame called
  from one that has bound nothing is the outermost frame and keeps the plain
  spelling.

The mint then checks its candidate against the memory the declaration lands in.
The counter is monotone and every generation it hands out is declared, so the
first candidate is free; checking anyway is what makes the invariant enforced
where it is created rather than trusted at the seventy sites that depend on it.

An inline body's frame retires the identities it minted for itself when it
returns, because it declared them into the caller's memory and nothing else
would: otherwise its cells stay readable under a later declaration of that name,
and a pointer to one of its locals stays dereferenceable at the call site. A
value-only parameter is deliberately left alone — its pseudo-slot borrows the
plain `local:<name>` spelling while owning no block, so retiring it would
tombstone whatever object of that name the caller has.

### When an automatic lifetime ends

An automatic object's lifetime ends when control leaves the block that
declared it. Its storage stops existing, so a pointer into it designates no
object and a load through one is undefined behaviour, not a way to read what
the block wrote.

The kernel has no statement that stands for a block — C0 lowers a source block
to a `Seq` tree — so a scope's own declarations are the `Declare` and
`DeclareAggregate` statements reachable from its root through that tree.
`scope_declared_names` collects them, stopping at a nested scope, which retires
what it declared itself. The cost of a scope exit is therefore the declarations
of the scope being left, not a walk of the frame's locals or of memory.

The scopes the kernel's own execution rules know are an `if` arm, a loop body,
and a `switch` body — one block for all of its cases, because control falls
from one case into the next. Every outcome of a scope's body leaves that scope,
so the retirement applies to all of them: falling off the end, the back edge,
`break`, `continue`, `return`, a jump, a thrown outcome. The name is unbound
with the storage, because the frame no longer holds an object of that name and
a later declaration of it is a declaration rather than a re-entry the mint
would tombstone from.

The surface stepper records `CheckedAutomaticLifetimeEnd` when its source
layout leaves a scope. The layout indexes normal and abrupt exits once; each
exit visits only the declarations it retires. The event retains the exact
before and after states; branch validation and return certification check the
retirement. This includes a `for` initializer's scope. The saved loop-exit
snapshot still names its final index for proof provenance; the subsequent
execution state has retired its storage.

A lowered `ForStep` ends the body locals before evaluating the update clause,
including on `continue`. A normal fallthrough update keeps its normal outcome;
a continue update resumes the loop head. Nested loops keep their own control
edges. A non-inline function also retires its body locals before postconditions
are read, so exporting an address through a field or output parameter does not
extend its lifetime. Address-backed scalar parameters expire too. Aggregate
parameter storage expires before postconditions and returned resources are read.
`SpecExpression::AggregateFieldValue` reads a direct by-value parameter projection
from its current storage while live, or its retained entry value after exit.
The existing check against postconditions reading modified parameter fields
still applies. The operation accepts a named object projection, not a loaded or
aliased C pointer; it creates no memory view or resource. Pointer-valued fields
are shallow values: a following dereference uses current C memory and requires
its own permission. Historical field reads resolve the object's address in the
selected entry snapshot. Materialized aggregate results belong to the caller
and survive the callee's exit.

The positive field, array, shallow-pointer, and aggregate-return checks are in
`mdtests/aggregate_parameter_value_fields.md`. The output-pointer, explicit
address-taking, and pointer-bearing return regressions are the other
`aggregate_parameter_*.md` fixtures. Kernel checks cover forged projections and
work independent of unrelated locals; positive proofs expand and recheck.

Value-only parameter bindings use a separate pseudo-slot namespace. Concrete
callee store events refresh the caller's affected scalar bindings by slot, so
a write through `&local` is visible when the caller next reads that local.

Memory mutation facts pair every written address with its byte width. Branch
joins preserve those pairs, and conversion to effect ranges preserves their
widths. Framing and mutable-footprint checks compare complete accesses rather
than only their starting addresses. Resolving a load to a stored scalar requires
the load's recorded width to match the stored value; a width-less term cannot
choose a cell type implicitly.

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
call application escrows the caller's owned resource, or reborrows its existing
view, and the return recovers it without creating a persistent view. Retiring
an allocation also consults the loan ledger on every path, so a live borrow of
any part of an allocation refuses the `free` or the undecided-continuity
realloc that would invalidate it. Thus a borrow from ownership ends before a
following `free`, while a view that survives the call must be proved separate
or causes `free` to fail locally. Deallocated
identity tombstones make use-after-free and double-free explicit, but carry no
resource authority. `HeapAllocated` and `HeapFreed`
memory derivation DAG edges preserve these transitions for later checking; an allocation
resource that crosses a verified call also determines the allocation delta,
not an untrusted ordinary token. When that delta leaves continuity undecided,
the input allocation's cached values and zeroed status are forgotten under
proven-equal pointer spellings. A `ContractAllocationRetired` edge records the
possible release without claiming that a C `free` occurred. Exact execution
records every successful
free as `CHeapAllocationFreed(before, after, base, bytes)`. Effect
certification checks that executing `free(base)` from `before` with the stated
extent produces `after`, and chains that transition separately from ordinary
`CMemoryMutatesOnly` and ranged call-havoc effects. This lets a function free
owned storage directly even when its surface `owns` clause names only
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

A `CallHavoc` edge carries the callee's checked owned ranges. Load transport
may cross that edge only when the loaded address is proved disjoint from every
range; multiple opaque calls compose by following the corresponding bounded
effect chain. This rule preserves an adjacent unchanged field without exposing
havoc block names in an expanded proof. A dependent address is transported
only when its pointer and index expressions are themselves stable. An
overlapping or undecidable footprint stops the transport.

Loop havoc carries the checked owned ranges of a whole-loop frame summary
when they are available. Its memory-DAG edge is crossed by the same
range-disjointness rule; a loop with no evaluated footprint remains a barrier.

Independent whole-path checking can regenerate fresh return variables and
`call-havoc` marker identities for the same execution path. Certification
couples those encodings only through matching memory-derivation structure:
local bookkeeping edges are transparent, stores must have equal pointers and
values, and call-havoc edges must have definitionally equal owned ranges and
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

A pure theorem becomes a universally quantified fact for whole-contract
certification only through the completion its checked proof already issued.
The kernel constructors
(`prove_universally_quantified_pure_implication` and its
`_by_int32_rewrites` variant) do not prove the conclusion a second time: they
check that the completion's goal is exactly the declared conclusion, that the
facts its root branch assumed are exactly the declared requirements, and that
the declared binders are exactly the free variables. The rewrite variant
additionally cites each equality it applied, which must be exactly available
among the requirements and must rewrite the goal in the listed order. A proof
the kernel proof object does not check, such as a script the legacy pure
driver accepts, publishes no such authority.
