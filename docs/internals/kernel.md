# Kernel implementation map

This page is for agents modifying Rust implementation, not for users writing
Click specs.

The shared execution representation uses `ProgramValue`, `ProgramType`,
`ProgramExpression`, `ProgramStatement`, and `ProgramFunction`; C, C++ and Rust
frontends all lower into it. `ExecutionState` supplies the locals, memory and
resources used to evaluate a program expression. A successful evaluation
produces a `ProgramValue`, which may contain symbolic kernel terms.
Surface/kernel names identify representation layers; program/spec names
identify roles within those layers. C-specific source syntax and effective-type
compatibility retain their C names.

## Core files

- `src/kernel/`: proof terms, shared program semantics, assumptions, symbolic execution,
  and theorem-producing functions.
- `src/languages/interface.rs`: shared `ImportedFunction`, `ImportedParameter`,
  `InterfaceType`, callback metadata and record layouts. `InterfaceType` retains
  declaration compatibility information that the kernel `ProgramType` erases.
- `src/languages/c/syntax.rs`: C parser and lowering to shared program terms. The
  parser's global declarations, type declarations and initializers are in
  `syntax/global_declarations.rs`, `syntax/type_declarations.rs` and
  `syntax/initializers.rs`.
- `src/surface.rs` and `src/surface/`: Click parser (`parser.rs`, `parser/`),
  validation (`validation/`), lowering (`lowering/`), tactics, and proof
  orchestration.

`src/kernel/mod.rs` defines real Rust submodules and re-exports the public
surface from `api.rs` and `primitives.rs`. Cross-module implementation helpers
stay kernel-private with `pub(super)`, and the private `prelude` module keeps
shared imports local to the kernel.

Kernel files:

- `primitives.rs`: core terms, program values/state, propositions, path structs, and
  basic data-type impls.
- `assumptions.rs`: `PureFactContext`, proof obligations, execution-derived pure
  facts (`ExecutionPureFact`), and symbolic execution accessors.
- `api.rs`: public statement constructors and theorem-producing entry points.
- `program_expression.rs`: constructors for the shared executable expression
  model, including literals, arithmetic, memory reads and explicit casts.
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
- `eval.rs`: program expression/statement evaluation and memory operations.
- `loops.rs`: loop verification, loop effects, loop havoc, and invariant
  helpers.
- `machine_integer/`: the correspondences between machine-integer and
  `Integer` facts, each stated once over a format; see "Machine-integer
  rules" below.
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
  Its children hold self-contained parts: `authority_contracts.rs` (calls
  whose contracts touch populations, mutexes and authority resources),
  `contract_refinement.rs` (whether an interface refines a named contract),
  `named_contract_refinement.rs` and `refinement_side_conditions.rs` (checking
  a function against a named contract), `call_arguments.rs` (binding and
  coercing a call's arguments and result), `globals_and_aggregates.rs` (entry
  storage and aggregate values), `composite_expansion.rs` (composite resources
  and their member facts), `instance_case_selection.rs` (which case of a
  matched resource instance applies) and `resource_clause_worklist.rs` (the
  indexes that order resource clauses).
- `tests.rs`: kernel unit tests.

## Trusted shape

`Theorem` is an abstract object. Callers can inspect its proposition but cannot
construct arbitrary theorems directly. Public functions that return `Theorem`
are trusted theorem-producing operations. In Click terminology these are
axioms, even when Rust names them `prove_*`.

### Source obligations and checked evidence

The Rust module boundary is not the whole trusted computing base. As described
in [Architecture](architecture.md#trust-and-boundaries), translating an accepted
source claim into the right kernel obligation is trusted too. This includes
choosing the entry state and symbolic inputs for a function contract. Smart
planning chooses steps for that obligation; it cannot change the obligation or
manufacture evidence for it.

For ordinary function contracts, the responsibilities are:

| Stage | Responsibility | Implementation |
| --- | --- | --- |
| Entry lowering | Represent the declared parameter domain and entry resources, without specializing to a convenient call | `initial_call_state` in `src/surface/lowering/resource_lowering.rs`, called by `initial_claim_context_with_caller_owner` in `src/surface/proof.rs` |
| Checked proof transitions | Validate execution, logical steps, branches, and completion against the supplied obligation | `src/kernel/proof/` and kernel execution APIs |
| Contract registration | Check artifact reuse, entry-case/path coverage and retained proposition/resource/effect completions; independent execution-only APIs check the supplied execution instead | `src/kernel/api.rs` and `src/kernel/api/contract_certification/` |
| Rule packaging | Require the complete set of certified claims for the exact function | `program_verified_function_rule` in `src/kernel/api/contract_certification/contract_claims.rs` |

Entry lowering gives separate scalar parameters separate symbolic variables.
Pointer inputs have separately named symbolic addresses; different names do
**not** establish unequal addresses or disjoint storage. Any alias restriction
must come from the applicable contract and resource semantics. Certification
uses the entry retained by the proof, including checked storage authorities;
it does not replace the supplied arguments with a newly generated generic
tuple. Rule packaging checks claim coverage and function identity, not the
source-to-entry translation again.

A proof about one call and a proof of a function contract have different
scopes. Checking a body at `x = 0` can establish a property of that call. To
justify a reusable contract with no restriction on `x`, the entry must represent
arbitrary permitted `x`. Callers of the low-level certification APIs that
intend to install reusable rules must preserve that generality. The current
Surface path constructs it during entry lowering; the API names alone do not
assert that arbitrary supplied states and arguments have been generalized.

When investigating a suspected boundary violation, identify the exact judgment
and its premises, the operation that issued the evidence, and which inputs the
caller was responsible for constructing. Kernel tests can access private
constructors and helpers, unlike Surface proofs. In particular,
`certify_contract_with_kernel_artifacts` accepts a test's state and arguments;
it does not run Surface entry lowering. Acceptance of a rule in such a test is
not, by itself, a demonstration that Click verified a false source claim.
Conversely, a kernel API that violates its stated judgment is a defect even
without a Surface reproducer. Neither the `verified` prefix nor membership in
the trusted implementation settles that question.

### Built-in arithmetic theorems

The machine-integer kernel standard theorems of `library/integer.click` are
`int32_remainder_to_integer`; the `uint32` and `uint64` divide and remainder
observation laws; the seven 16-bit packing
laws; and `uint32_from_le_bytes`. Each is a kernel axiom built by a `prove_*`
operation that constructs only the fixed implication documented in the
standard library. Standard-library verification (`verify_standard_library`,
run by the gate) checks each parsed declaration against its exact
proposition. No certificate rule relates a machine `/` or `%` with a
symbolic divisor to its `Integer` value, so those laws remain axioms. The
eight `to_*_round_trip` laws are proved: `integer_cast_identity` reads
`to_integer(to_T(z))` as `z` from `z`'s two bounds inside `T`'s range, once
for every format (`conversion::integer_conversion`). The `int32` increment,
predecessor, order and definedness lemmas, the in-range `+`, `-` and `*`
observation laws, the `uint32` product-guard, remainder and
wrapping-difference laws and the `uint64` order transitivities are proved
library theorems instead, with pinned explicit proofs (the `uint32` product,
guard and remainder laws apply the division observation axioms and the
truncating-division lemmas), and add no kernel operation. The prelude and the kernel ship in one executable, so
ordinary verifications apply these declarations as dependencies without
re-checking them; expanded user proofs use the ordinary simple
`apply(...) using { ... }` tactic.

### Execution and contract evidence

Execution theorems retain every verification condition as an implication
premise, including conditions that are not assumable during execution.
`FunctionExecutionCandidates` is deliberately theorem-free: interpreter- or
caller-supplied outcomes are only candidates until a kernel execution
reproduces them.

Opaque function rules have a narrower boundary:

- the rule is bound to the complete `ProgramFunction`, including its lowered body,
  contract, exact claim targets, resource definitions, and execution metadata;
- `FunctionContractExecution` can only be created by the kernel from the
  exact function's entry state and contract-derived assumptions. The kernel
  builds the contract entry (`program_function_contract_entry`): its lowering of
  each `requires` clause, the parameters' ranges, and what the entry
  resources state, each fact tagged with its origin. A proof starts from
  that entry, seen through the source spelling the proof side recorded, with
  facts nested inside a resource or a predicate body out of view until the
  proof observes or unfolds them. A caller applying the rule discharges the
  same lowering, so the body is proved from what its callers establish.
  Certification reuses a proof's execution when the entry states each of its
  assumptions, which is a lookup;
- contract execution mode is explicit. `VerifyLoops` checks annotated loop
  rules, while `ExecuteLoops` unrolls loops along a bounded execution;
- every path verification condition is discharged before any body-safety,
  postcondition, resource, or effect claim is certified;
- all recorded contract claims must have checked evidence for that same exact
  function before `VerifiedFunctionRule` can be constructed;
- contract instantiation uses simultaneous, capture-avoiding substitution,
  and alpha-equivalence freshens both sides before comparing bound bodies;
- composite-resource fold facts are rechecked against the kernel resource
  state even when a resource body has a guard, so surface lowering cannot
  turn a captured fact into resource authority.

If contract closing cannot complete every applicable obligation, or registration
cannot associate the retained completions with every entry case, Click installs
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
to an untrusted `FunctionTerminationPlan`; the kernel checks the exact
partially verified function bodies, loop indices, integer types, guards, and
decreasing edges before constructing `VerifiedFunctionTerminationRule`. The
two rules stay separate in the environment: applying a
`VerifiedFunctionRule` never consults termination evidence, so the demand is
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
component travels on the function's `FunctionContractInterface`, beside its
`contract_requires`, because the call site is where the descent is owed. At
the entry of the function being certified the kernel reads that component once
and installs a `RecursionAnchor { function, component, measure: M0,
entry_obligations }` on the `ExecutionEnvironment`; the anchor has no public
constructor, and `program_execution_environment_with_recursion_anchor` reads the
measure off the named function's own interface, so asking for an anchor cannot
choose what it ranks. At a call step whose callee is the anchored function,
`prepare_verified_function_call` reads the same component at the state the
callee's preconditions are read at and emits `0 <= m` and `m < M0`, plus the
viewability the two readings owe, as ordinary verification conditions. A proof
that does not discharge them does not get past the `step()`, and one that
somehow retained them carries them as premises of its path theorem.

The anchor is part of `ExecutionEnvironment`'s identity. Contract
certification derives it itself from the function and arguments in hand rather
than trusting the caller's, and reuses a checked artifact only when
`checked.environment == environment`, so an execution stepped without the
anchor — which raised no descent obligation at its self-calls — is not reused
to certify a contract whose function declares a measure. `checked_function_execution`
refuses such an execution outright as well. What is left for the termination
judgment is that the obligations were reachable and complete: the certified
`ProgramFunction` must carry the measure (the plan names only a spelling, and
`program_verified_function_rule` binds every claim to the same `ProgramFunction`), the
component's only recursive edge must be the self-call, and the function must
not have an inline body. Both are refusals by name; `decreases <int32
parameter>` still ranks those shapes.

A loop is verified as its own judgment and then applied as a summary, so a
self-call inside one is a call no step of the function's own proof takes. The
loop's body is certified under the same anchor instead: a claim's proof asks
the kernel for it from the function in hand before its first step, and the
`loop` tactic plans its loop in that proof's environment, so every loop of
that function — nested, inside an `if`, or inside a `switch` — is stepped
with it and a self-call in the body raises the same two members against the
same function-entry M0. M0
survives the loop's havoc because it is a closed term over entry symbols and
`collect_execution_environment_variables_uncached` reserves every variable it
names, so no fresh iteration value is handed out on top of one; a measure that
reads memory names the entry memory state, and only an invariant the user
writes relates the iteration's reading to it.

`VerifiedLoopRule` records the anchor its own body was stepped under. The
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

A loop back edge must also preserve any object class retained for a pointer
local at the head. A class mismatch names the first failing local and prints
the head and back-edge classes. A missing back-edge class is reported as
`unknown (no retained object class)`, distinct from an unbound local. Class
printing uses nominal struct tags, pointer base/depth, and member/scalar classes,
without dumping struct layouts. The diagnostic retains the comparison already
made by the join checker; it does not scan locals a second time.

The join never supplies a missing class, so every way a pointer reaches the
back edge must carry one. These sources carry a class:
- C declarations: parameters, declared locals, struct-pointer member loads
  and call results.
- The Click declarations listed in
  [effective types](https://github.com/clicklang/click/blob/master/design/effective-types.md#status): model fields,
  Click function results and theorem parameters.
- An integer word whose origin fact names a classed address. Decoding it
  through tag masking restores the class.

A pointer that has no class here also gets no strict-aliasing checks. The
fix for such a pointer belongs where it was formed, not at the join. For
example, the null constant has no class, so assigning `NULL` to a classed
local inside a loop is refused today
([bug](https://github.com/clicklang/click/blob/master/bugs/null-assignment-in-loop-fails-object-class-join.md)).

A loop ranking component is not restricted to a C expression. The loop head
carries a `RankingComponent`: a current-state C expression, a pure
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
readings of one component always agree on it. `ranking_measure_term` returns
a `RankingMeasureValue`, `Machine` or `Integer`, and the members are built in
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
(`RankingMeasureKey::Pure`), which is a weaker match than the structural
equality a C component gets, because the whole-function plan is built before
specification lowering has an environment. The weaker match is not soundness
relevant. Termination evidence is the certified loop's own back-edge bundle,
which discharged `0 <= m` and `m_post < m_pre` for the component the kernel
holds on that rule's loop head; a loop with a nonnegative int32 quantity, or
an unsigned machine quantity under unsigned order, that strictly descends on
every back edge terminates whichever quantity it was.
The plan only says which loop to point at, and a rule is bound to its source
loop by index and executable shape, a comparison that ignores the measure.
Matching the measures on top of that turns a plan describing one measure and a
certificate carrying another into a named refusal instead of a silent
mismatch, so weakening it can cost a diagnostic and not a theorem. A
component that names a proof binder, such as a `let { field: name } =
unfold(...)` name or a proof `match` payload, resolves at the loop head to the
value the binder stands for, so the loop head carries it as a pure component
under its written spelling while the plan, built from the same written clause
before any proof runs, reads that spelling as a C expression; the check
accepts a pure key whose spelling is the planned C expression's display. The
address-escape refusal, the one place the plan's measure is read for more than
identification, runs on the certified side for a pure component, where the
lowered expression is available; a lowered form whose C variables cannot be
collected is refused rather than passed unchecked.

Termination rules live in their own execution-environment map. Constructing or
applying `VerifiedFunctionRule` does not consult that map, so a termination
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

When two certified execution paths use different memory states, resource
representation comparison unfolds each composite against its own state.
Unfolding replaces the folded parent with its children while they are
evaluated; keeping both parent and children would create a false ownership
overlap. The composite definition supplies the checked `contains` and
`separate` relations used to compare the resulting child contexts.

## Important types

In `src/kernel/`:

- `MachineTerm`: the one term arena for every C integer and float value,
  including arithmetic, `If`, `RangeFold`, and memory loads. Despite its
  name it holds every width. A machine operator is a format-carrying
  `Binary { op, format, .. }` or `Unary { format, op, .. }` node
  (`MachineBinaryOp`, `MachineUnaryOp`; signed and unsigned division,
  remainder and right shift are told apart by the format) at a 32- or
  64-bit format. A constant is one format-carrying node,
  `Constant { format, bits }`, for every format (decision G9): build it with
  `MachineTerm::constant` (`int32`), `uint32_constant`,
  `int64_constant`, `uint64_constant` or `machine_constant`, and match it
  with `int32_constant!`, `uint32_constant!`, `bits32_constant!` (either
  32-bit format), `int64_constant!`, `uint64_constant!`, `native_constant!`
  (8, 16 and 128 bits) or `Constant { .. }`. A pattern binds the `u128`
  bits; read them with `constant_u32`, `constant_i64` or `constant_u64`, the
  value types the per-format constants had; `Debug` still prints the
  per-format variant names. Code that hashes or compares
  nodes by discriminant also takes a constant's format. A conversion is one
  node, `Cast { spelling, value, from, to }`, whose `MachineCastSpelling`
  (shared with the kernel term's `MachineCast` encoding) is `Generic` or
  one of the six legacy per-pair spellings (`Int64From32`, `UInt64From32`,
  `UInt32From64`, `Int64FromUInt32`, `UInt64FromInt32`, `UInt64FromInt64`).
  The spelling is part of the identity, so a legacy-spelled conversion and
  the generic one of the same formats are different terms. A legacy
  spelling fixes its formats (`MachineCastSpelling::legacy_formats`); the
  low word reads its operand as `uint64` bits whatever the operand's
  signedness. Build one with the smart constructors
  (`machine_integer_cast`, `int64_from_32`, `uint32_from_64`, ...),
  `MachineTerm::legacy_cast` or `cast_node`; match a legacy spelling
  with `cast_term!(Int64From32, value)` (`cast_op!` for its
  `BitvectorUnaryOp`) and the generic one with
  `Cast { spelling: Generic, .. }`. `Debug` prints the former variant names,
  and `machine_operator()` returns the spelling for discriminant-based
  comparisons and hashes. Every operator of a
  `uint32` value is built at `uint32` over operands and constants in that
  format, through
  the format-parametric constructors (`add_at`, `subtract_at`, ...,
  `machine_binary`); the width check refuses any other format. An operand
  keeps its structure: σ and a narrow widening are nodes of their own
  (rule K1 and K8's peels are deleted), and the e-graph, the difference
  graph, the signed interval rules and the representation map read a
  32-bit sign-free operator by its bits at either format, relating σ to
  its operand (R0, R-dist, the difference graph's σ link). A `uint32`
  constant is read as the `int32` constant of its bits inside an `int32`
  operator, comparison or overflow test (`into_word32`). Code that compares
  nodes by variant also compares
  `machine_operator()`, since one variant spells every operator. This word
  identity is being removed (`design/machine-integers.md`, "Every format
  its own nodes"); a debug build with `CLICK_FORMAT_AUDIT=<path>` records
  each remaining use of it by kind and site (`scripts/format-audit.sh`,
  `machine_integer/format_audit.rs`). Elsewhere
  the width is implied: by a load's kind or a cast's destination. Values of
  8 and 16 bits, and a `Bool`'s cast `b as F` to a narrow `F`, ride in the 32-bit carrier, and floats in the
  carrier of their bit width. `term_width.rs` infers that carrier width.
  Debug builds refuse a condition assumed into a fact context, a value an
  expression evaluates to, or a value stored to memory whose widths disagree:
  an operand of the wrong width, arms of different widths, a `ProgramValue` tag
  whose term has another width, or a comparison whose operands are not the
  width it names. The one exception is a load equation (a store fact or a
  load variable's defining fact), written with the 32-bit equality at any
  width, whose sides need only agree with each other. A variable records no
  width either, so each fact context remembers the width its facts use each
  variable at, and debug builds also refuse a condition that uses one at
  another width. The scope is the context, not the run: variable numbers are
  assigned per function, and two facts only combine within one context.
  Debug builds also refuse a narrow value whose word is not the canonical
  carrier of its format (see "One meaning for a narrow value" below). Why
  the width stays implied instead of part of the term is ruled in
  `design/typed-indices.md`.
- `PointerOffsetTerm`: pointer-offset expressions.
- `ConditionTerm`: proof-level truth-valued conditions: machine comparisons
  `Compare { format, relation, left, right }` and overflow tests
  `Overflows { format, op, left, right }` at every machine-integer format,
  `Integer` comparisons, pointer-offset and pointer equality, and typed IEEE
  floating comparisons/classifications. An equality is filed at the signed
  format of its width (it reads no sign), and a narrow comparison at
  `int32`, whose order its canonical words compare exactly, so a fact has
  one spelling. Every other order is filed at its own format: a `uint32`
  order is `Compare { format: UInt32, .. }` of the operands' words.
- `ProgramValue`, `ProgramType`, `Pointer`, `Memory`, `ExecutionState`: C semantic state,
  including the non-object `Void` return value, scalar `int8`, `int16`, `int32`,
  `uint8`, `uint16`, `uint32`, `int64`, and `uint64`, pointers, and typed
  memory loads/stores.
  Kernel execution reports
  `TypeMismatch` if `Void` is used as a condition or object type; it never
  erases that execution path.
- `ProgramExpression`, `ProgramStatement`, `ProgramFunction`: lowered C syntax. Calls have
  distinct assigned-result and discarded-result statements; a normal
  fallthrough from a `void` body completes with `ProgramValue::Void`.
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
- `FunctionContractExecution`: kernel-produced complete execution evidence
  used only for exact opaque-contract certification.
- `VerifiedFunctionContractClaim`, `VerifiedFunctionRule`: unforgeable
  evidence for one exact claim and for a complete exact opaque contract.
- `FunctionTerminationPlan`, `VerifiedFunctionTerminationRule`: respectively
  an untrusted ranking proposal and separate kernel-checked evidence that the
  exact partially-correct function returns.

The current integer conversion slice is deliberately small. `eval.rs` promotes
`int8`, `int16`, `uint8`, and `uint16` rvalues to `int32` terms for arithmetic, ordered
comparisons, shifts, and bitwise operators, assignments, and returns.

### One meaning for a narrow value

A term of an 8- or 16-bit format (`int8`, `uint8`, `int16`, `uint16`) is a
value of its own width (`CarrierWidth::Bits8`, `Bits16`), not a 32-bit word
(step 7 of `design/machine-integers.md`; maintainer directions of
2026-10-30, 2026-10-31 and 2026-11-01). `to_integer` of it is its value in
its format, and its range is its format's: no range fact is filed for it.

- A constant is a native `Constant` node of its format; the
  equality graph keys narrow constant atoms by their bits at the unsigned
  format, so `int8` -56 and `uint8` 200 are one node, and folds a cast of a
  constant class to the destination's constant.
- A binder (a parameter, a theorem or quantifier binder, a value a loop or
  call produced) is a variable at its format; its range is its format's.
  A premise that holds by that range alone (`0 <= x` for a `uint8` `x`, or
  `widen(x) >= -128` for an `int8` `x`) is available to every `using` list
  (`holds_by_format_range`, one match at the root); a goal that holds by
  it is closed by `normalize()`.
- Every narrow load is its own load at its own type: the read's variable is
  registered at its kind, the equality graph names it by its exact cell,
  and it is a load application of its state, address and kind
  (`Application::NarrowLoad`), equal to a stored value of its width
  (`CellRead::Narrow`). The `int8` and `uint8` reads of one byte are two
  loads related by the 8-bit sign cast (byte R-mem). A read of a canonical
  projection is joined to the same read of its recorded source by one
  indexed edge (`Node::NarrowRead`), as a four-byte read is. Byte views
  produce `(v >> 8k)` as `uint8`.
- Every conversion into a narrow format is a generic `Cast` node (or
  `IntegerToMachine` from an Integer), from the conversion table
  (`machine_integer::conversion::lower`, `convert_term`). A checked
  (`Standard`) narrowing owes the destination range as obligations and
  files the certified identity `to_integer(conv(w)) == to_integer(w)`
  beside them (`checked_narrowing_identity`).
- A 32-bit view of a narrow value is its widening, `Cast(S -> int32, v)`,
  related to `v` by value (K8, a relation across widths), never merged with
  it. Its observation `to_integer(x as int32)` is built as written, and rule
  W relates it to `to_integer(x)`: the Integer engines read the two as one
  atom, and `integer_cast_identity` accepts `to_integer(widened) ==
  to_integer(x)` with its bounds checked at `x`'s format.

C compares narrow values through their promotions, which is its structure:
a C comparison of bytes is the signed `int32` comparison of the widenings.
In this PR a specification or Rust comparison of narrow values is promoted
the same way (maintainer direction, 2026-11-01); native specification and
Rust comparisons come with the order and interval reasoning that reads a
native narrow fact as a bound on its widening. A promoted comparison of
widenings has one Integer reading, the comparison of its sides' values
(`machine_integer::comparison::integer_readings_with_promotions`):
`0 <= widen(x)` is `0 <= to_integer(x)`. The Integer engines
(`integer_affine_claims`), the certificate's premise check and the smart
planner's spelling read it like a native comparison's reading. The
certificate checker reads an 8- or 16-bit comparison as the `int32`
comparison of the widenings (`narrow_comparison_as_int32`).

A universal over a promoted comparison of a read instantiates against a
goal's read through the widening: `guided_forall_condition_candidates`
matches a conversion node against the same conversion structurally, one
node per step (`mdtests/byte_slice_range_predicates.md`).

Scalar `uint32`
addition, subtraction, and multiplication use the same 32-bit operator
nodes as `int32`, without signed overflow obligations: the operators read
words. A conversion between `int32` and `uint32` is the sign cast σ, a
generic `Cast` node of its own (step 4b of "Every format its own
nodes"): operators, comparisons and observations keep it as written, the
e-graph relates it to its operand by R0 and R-dist, the difference graph
links either 32-bit reading of σ(x) to the same reading of `x`, rule W
reads an observation of it as its operand, and only an element index
peels it, in `int32` index coordinates (`into_index_word32`, decision G1)
(`docs/internals/mathematical-integers.md`, "The 32-bit sign cast"). A
32-bit load has the reader's signedness (`LoadKind::Int32`, `UInt32`; a
pointer read is `Int32`), and a typed read of a cell stored at the other
signedness returns σ of the stored word (rule K5), and so does every route
that answers a load term from a cell or a store (`LoadKind::read_cell`;
`LoadKind::reads_value` holds only at the stored kind); the two reads of one
cell are two loads, the `uint32` read σ of the `int32` read (R-mem).
A `uint32` constant is the `Constant` node at `uint32`, an `int32` or
kernel-internal one the node at `int32`; inside a signed operator or
comparison it is read as the `int32` constant of its bits. An equality of `uint32` values is a `uint32`
term as written, and the same fact as the `int32` equality of the same bits
at the fact-identity and lookup-key level only (rule K6). Unsigned division and
remainder have distinct term nodes so high-bit operands do not inherit signed
division, and unsigned right shift has a distinct logical-shift node. Equality
and ordered comparisons select the unsigned conditions. Stores and function
returns preserve the `uint32` type tag. Scalar narrowing in C is GCC's
modulo 2^N conversion at every boundary and adds no obligation; into a one- or
two-byte type it yields a generic `Cast` node, filed with the
destination's range, which is the operand's carrier once the operand's range
is known (`narrowed_cast_identity`). A conversion between the two
signednesses of one width changes no bit, so its signed reading is negative
exactly when its unsigned reading exceeds the signed maximum: the decision
procedure and the known-condition lookup read each test as the other, at
8, 16, 32 and 64 bits (`condition_reasoning/sign_bit.rs`; at 8 and 16 bits
once the operand's range is known). C++20 integral conversions and Rust `as`
build the same node and file the same range. A specification's cast is the same
modular conversion; a checked conversion is written `to_T(...)` and owes the
destination range. A checked narrowing cast yields the same node, with the
identity fact described above. `int8` occupies one byte with
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

Scalar specification guards containing `and`, `or`, and `not` are encoded with
existing 0/1 conditional terms, visiting each guard node once. The selected
value's arms occur once around that guard, rather than being duplicated
through the logical tree. Lowering remains context independent; explicit
normalization uses the stated premises to select an arm. Unknown guards keep
both possibilities (`mdtests/pure_conditional_compound_guards*.md`).

### Machine-integer rules

`src/kernel/machine_integer/` states each correspondence between machine
and `Integer` facts once, as a function of the format
(`MachineIntegerType`, a name for a `MachineIntegerFormat`). No caller lists
the widths a rule supports; it asks the module
(`design/machine-integers.md`, "Rules stated once over a format").

| Rule | Module function | Statement |
|---|---|---|
| Exact comparison | `comparison::native_comparison_of_integer_observation`, `integer_observations_of_native_comparison`, `native_comparison_through_integer_operations` | `to_integer(a) R to_integer(b)` holds exactly when the native comparison of `a` and `b` at their format does |
| Range | `range::range`, `range_fact`, `constant_word` | `min(F) <= to_integer(v) <= max(F)` |
| In-range identity | `identity::mathematical`, `machine_operation_of_integer_value` | `to_integer(a op b) == to_integer(a) op to_integer(b)` for `+ - *` when the exact result lies in `F` |
| Operation bounds | `bounds::operation_bound` | a quotient, right shift or remainder by a positive constant, against its operand |
| Definedness | `definedness::integer_bounds_of_definedness`, `overflow_fact_of_integer_bound`, `definedness_of_integer_bound`, `defined_formats` | `not overflows(F, op, a, b)` exactly when the exact result lies in `F`; facts are filed at `int32` and `int64` only |
| Modular equality | `modular::wrapped_equality_at`, `wrapped_equality_of_integer_equality` | an `Integer` equality over `+ - *` of observations of width `w` implies the word equality modulo `2^w` |
| Conversion | `conversion::cast` and the narrow-widening helpers | a cast preserves a value its destination holds; a widening needs no premise |
| Conversion table | `conversion::lower`, `convert_term`, `convert_value` | the node a conversion from `S` to `F` builds in every language, and whether a specification's conversion owes the range |
| Usual arithmetic conversions | `conversion::usual_arithmetic_format` | C11 6.3.1.8 in LP64: the format two integer operands are converted to, after promoting narrow formats to `int32` |
| Narrow widening (K8, a relation) | `primitives::is_narrow_widening32`, `MachineTerm::narrow_widening32_operand`; the e-graph's value link and its sibling relation (`machine_relations::relate_siblings`); the difference graph's `link_parts` and `structural_interval`; rule W below | `Cast(S -> F, v)` for a narrow `S` and a 32-bit `F` has `v`'s value: `to_integer(widen(v)) == to_integer(v)`, a link with `v`'s range, never a union across widths. The `int32` and `uint32` widenings of one value are two nodes: where the e-graph has both, the later is joined with σ of the earlier (R-comp read backwards, one node and one union), so σ relates them and distributes over the earlier one's operators; neither is joined with the other |
| Observation value relations (W) | `SharedMachineIntegerTerm::value_reading`, `machine_value_reading`, `IntegerTerm::value_read`, `SharedIntegerTerm::read_through`; the readers: Integer affine atoms (`collect_integer_affine_terms`), `ConditionTerm` identity of Integer comparisons, `range::observation_range`, `native_comparison_of_integer_observation`, `native_comparison_through_integer_operations`, `identity::mathematical`, `conversion::cast`, the Integer rewrite's occurrence match | `IntegerTerm::from_machine` builds an observation as written and folds no conversion; its value is related, not rewritten: `to_integer(widen(v)) == to_integer(v)` for a value-preserving widening at any width, `to_integer` of σ(x) at `int32` or `uint32` is `x` read at that format, and a conversion observed at a type containing its destination is observed at the destination. The reading is computed once per interned observation (at most three conversions) and per Integer node (`read_through`), cached on the node, so each reader's step is O(1) after the first; terms are printed as written |
| Native narrow nodes | `CarrierWidth::Bits8`, `Bits16`, `CarrierWidth::native`, `is_native_narrow_operator`; `MachineTerm::narrow_constant`, `machine_binary`, `machine_unary`; the e-graph's `Node::MachineNarrow` and `narrow_constants` | an 8- or 16-bit operator `+ - * & \| ^ << ~`, constant, binder or load is a value of its own width, `(a op b) mod 2^N`; narrow constant atoms are keyed by their unsigned bits, a cast of a constant class folds to the destination's constant, and a narrow equation is decided by one class (true) or two different constants (false) |
| Narrow-cast word (K7') | `representation::narrow_carrier_mask`; the e-graph's `narrow_cast_node`, `narrow_cast_word` | the 32-bit widening of `Cast(S -> F, x)` into an 8- or 16-bit `F` at `w`'s format meets `w & m`, or `((w & m) ^ s) - s` for a signed `F`, with `w` the operand's word (`int32` or `uint32`), a 64-bit operand's `uint32` low word, or a narrow operand's widening (its `uint32` one where the graph has only that, else its `int32` one); the other widening is interned only where a term names it, and is then σ of the first by the sibling relation, so its word is σ of the masked word |
| Narrow loads and byte R-mem | `Application::NarrowLoad`, `CellRead::Narrow`, `Node::NarrowRead`, `enqueue_narrow_load`, `enqueue_signed_byte_read` | an 8- or 16-bit read is a load application of its state, address and kind, equal to a stored value of its width and, for a canonical projection, to the same read of its recorded source (one indexed edge); the `int8` read of a byte is `Cast(UInt8 -> Int8, u)` of its `uint8` read `u` |
| Promoted comparison reading | `comparison::integer_readings_with_promotions`, `integer_comparisons_of_widenings`; `integer_affine_claims` | a signed `int32` comparison whose sides are narrow widenings or constants is the Integer comparison of the sides' values (`0 <= widen(x)` is `0 <= to_integer(x)`); a native 8- or 16-bit comparison has the readings of its promoted spelling |
| Native narrow comparison (one fact, K8) | `ConditionTerm::comparison_fact`, `as_fact_comparison`, `ComparisonSide`; `comparison::narrow_comparison_as_int32`, `narrow_fact_widening`, `native_narrow_comparison`; `condition_match_key`; the `adjust_*` wrappers of `PureFactContext` and `EqualityGraph::add_condition` | a specification or Rust comparison `a R b` of two values of one 8- or 16-bit format `S` is native at `S`, and is the same fact as the `int32` comparison of the operands' widenings (a constant side in `S`'s range reads as its value): identity, hashing, order and every structural fact key read both as one, in O(1) per side; the 32-bit indexes also file a native fact under its `int32` spelling. Terms are built and printed as written; C comparisons and a written `x as int32 R c` stay promoted |
| Sign cast σ (K1 deleted) | `MachineTerm::sign_cast32`, `sign_cast32_operand`; the e-graph's `intern_conversion` and `convert_like` (σ an `Int32Unary::Cast` node); the difference graph's `link_parts` and `structural_interval`; `into_index_word32` (G1) | σ(x) between `int32` and `uint32` is a node of its own wherever a term is built: no constructor, observation, e-graph or difference-graph reader peels it. The e-graph relates it to `x` by R0 and R-dist (σ of a sign-free operator is the operator at the other format over σ of its operands; σ of a low word is that low word), the difference graph links either 32-bit reading of σ(x) to the same reading of `x` with offset 0, and an element index alone reads σ's operand in `int32` index coordinates. The constructor folds a constant and keeps σ of σ as written; R0 puts σ(σ(x)) in `x`'s class. Two smart-search readers see through one σ at a side's root: `σ(x) == x` is a vacuous rewrite and no rewrite candidate (`is_sign_cast32_of`, `equality_is_vacuous`, `connected_equalities`), and `σ(y) <=u c` below the sign bit is the signed range of `y` (`unsigned_upper_bound_below_sign_bit`) |
| R-mem at 32 bits (K5's naming deleted) | `ProgramType::read_cell`, `LoadKind::read_cell`, `LoadKind::reads_value`; the checked stored-value evidence (`CheckedLoadEqualityEvidence::OriginStoredValue`), `is_store_fact` | the `uint32` read of a cell is σ of its `int32` read; a read of a cell stored at the other 32-bit signedness, wherever a load term is answered from a cell or a store, is σ of the stored word, and only a read of the stored kind is the stored term itself. A range's `fits` guard is `σ(end - start) <=u limit` (`memory_range_byte_count_extent`), σ of the `int32` element count as written |
| Observation of σ (K2 deleted) | rule W: `machine_value_reading` | `to_integer` of σ(x) at `int32` or `uint32` keeps σ as written and reads as `x` at that format, through every σ of a written chain: `to_integer((a as uint32) as int32)` reads as `to_integer(a)` (`machine_view::shared_value_reading` takes one cached step per σ node) |
| 32-to-64-bit extension, one spelling | `conversion::extension_encoding`, `conversion::reads_as_operand`; `MachineTerm::machine_integer_cast`, `SharedMachineIntegerTerm::cast_operand`, `KernelTerm::checking_machine_cast`; rule W: `machine_value_reading`, `machine_view::shared_value_reading` | a conversion from `int32` or `uint32` to `int64` or `uint64` is the legacy-spelled `Cast` C lowering builds (`Int64From32`, `Int64FromUInt32`, `UInt64From32`, `UInt64FromInt32`) wherever it is built, never the generic spelling; `to_integer` of the three value-preserving ones at their destination reads as their operand, one match on the root. A cast-identity certificate checks an extension's bounds at its destination format |
| 32-bit equality one fact (K6, lookup-level) | `comparison_identity` (`ConditionTerm::comparison_fact`, `as_fact_comparison`, `fact_format`), `MachineTerm::sign_cast32_bits`; `condition_match_key` | a 32-bit equality is a term of the format it is written at, `u == v` at `uint32` over `uint32` operands; identity, hashing, order and every structural fact key read it at `int32`, each side through one σ and a constant of either spelling as its bits, so `u == v` at `uint32` and `u as int32 == v as int32` are one fact. One match per side, no clone; no term is re-filed |
| Sign test of σ (sign bit at 32 bits) | `condition_reasoning/sign_bit.rs`: `sign_bit_equivalents`, `names_sign_cast32` | `u as int32 < 0` is `u > 2^31 - 1`, and `x as uint32 > 2^31 - 1` is `x < 0`, the equivalent built through σ, reading σ of a σ as that σ's operand (the constructor keeps σ of σ); a decision or known-condition lookup of either reads the other, and assuming a test of σ also files its equivalent |
| Sign cast of a quotient (C) | `condition_reasoning/sign_cast_division.rs`: `decide_by_sign_cast_division`, `sign_cast_division_equivalent`, `names_sign_cast_division`; `MachineTerm::sign_cast_division_operands`; `ConditionTerm::nonnegative_division_bound_guards` | `(a / b) as int32 == (a as int32) / (b as int32)` for `uint32` `a`, `b` with `0 <= a as int32` and `0 < b as int32`, and `(x / y) as uint32 == (x as uint32) / (y as uint32)` for `int32` `x`, `y` with `0 <= x` and `0 < y`, and the same for `%`. Read at decision time on a comparison naming σ of a quotient, and filed beside such a fact when it is assumed: one match on each side's root and two sign decisions per side; the quotient bound guards read it too. A quotient by zero is not related |
| Cross-format relations (R0, R-dist, R-comp) | the e-graph's `terms/machine_relations.rs`: `relate_machine_application`, `merge_machine_relations` | a conversion to a format no wider than its source distributes over `+ - * & \| ^ ~` and a constant `<<` below the destination's width (σ, which keeps the width, over a `<<` by any count); a conversion of a value-preserving conversion it reads exactly, or one keeping no more bits than either, is one conversion; a same-width conversion of at least 32 bits has its inverse in its operand's class; where both 32-bit widenings of one narrow class exist, the later is σ of the earlier (`relate_siblings`) |
| Native narrow arithmetic (G2, G4) | `SpecExpression::NarrowArithmetic`, `SpecExpression::at_machine_type`; `IntegerCastMode::NarrowArithmetic`, `program_expression::narrow_arithmetic`; `IntegerCastMode::ResultConversion`; `eval::native_narrow_binary`, `native_narrow_not` | specification arithmetic `+ - * & \| ^ ~` at an 8- or 16-bit position (a typed `let`, a pure function's argument at its parameter's type, a pure function's body at its result type) over operands of that type, and Rust `+ - * & \| ^ !` and `<<` by a 32-bit count on `u8`, `i8`, `u16`, `i16`, are the native node of the type, `(a op b) mod 2^N`, with no promotion and no domain obligation; an `int32` literal the type holds takes it. Rust's checked overflow stays its own panic assertion. An operand of another machine type at a specification position is refused by the parser or type checker, which names the conversion to write; inside the kernel, operands of another type keep the promoted reading. C keeps promote, operate, convert |
| Promoted spelling of a native narrow operator (N) | the e-graph's `terms/machine_relations.rs`: `promote` (`Relation::Promote`) | a native 8- or 16-bit operator `a op b` (and `~a`, and `a << c` for a 32-bit count `c`) is in the class of `Cast(int32 -> F, widen(a) op widen(b))`, interned with its K7' word, so its widening meets the masked word operator. It fires on demand: when the operator's class is widened to 32 bits, and for a shift (whose symbolic count R-dist cannot move); C's spelling meets the native node through R-dist and R-comp without it. Once per operator, at most seven nodes and two unions; an operator R-dist built is skipped, and R-dist of the rule's own narrowing over its word is marked fired |
| `Bool` conditional (L-If) | `ConditionTerm::open_bool_if`; `PureFactContext::decide_bool_value` | `if c { a } else { b }` holds exactly when `(c and a) or (not c and b)`; opened only when the conditional itself is decided or split |
| `Bool` equality (L-Eq) | the e-graph's `bool_node`, `admit_bool_condition`, `knows_bool_condition` | a true `a == b` merges the classes of `a` and `b`, which share their truth; a false one contradicts the merge; applications of one function to equal arguments are one class |
| `Bool` unfolding (L-Unfold) | `ConditionTerm::bool_unfold_equation`; `unfold` lowers `f(args) == body` to `BoolEqual` | unfolding a `-> Bool` function's application files `application == body` |
| `Bool` to integer (C1) | `MachineTerm::BoolCast`, `bool_cast`, `bool_word_as`; the e-graph's `link_bool_cast`, `cast_value_truth`, `cast_disequality_truth`; `program_bool_cast_range_facts` | `b as F` is 1 when `b` holds and 0 otherwise: a decided `b` merges the cast's class with that constant, the constant 1 or 0 decides `b`, any other constant is a contradiction, a cast unequal to 0 or to 1 decides `b`, two casts in one class have equal `Bool`s, and two unequal casts have unequal `Bool`s; the cast's word is canonical at every format (C1c), and `0 <= b as int32 <= 1` with `b as int32 == 0 or b as int32 == 1` is filed where a C `bool` value is introduced (C1b) |
| Integer to `Bool` | `ConditionTerm::nonzero_test`, `bool_not` | C's `(bool)x`, an assignment or argument at `bool`, and a C++ conversion are the `Bool` `x != 0` (a non-null test for a pointer), the negation `if x == 0 { false } else { true }`, exact at every width; a cast `b as F` tested against zero is `b` |
| Byte rule | `eval::memory_loads::symbolic_load_value_unrecorded`, `canonical_integer_read`, `primitives::cell_store::cell_run_value` | a store of a `Bool` writes its byte `b as uint8`; a read of a `bool` cell whose byte is `β` is the `Bool` `β != 0`; no write of another kind and no byte view reaches a `bool` cell |
| Rust `Bool` values (D5) | `IntegerCastMode::BoolValue`, `program_expression::bool_value`; `eval::expression::ConditionValueScope` | a Rust comparison, `!`, or connective of a local or a value is the `Bool` it tests, carried as its C1 cast, with no path split; a branch or loop condition stays the comparison it tests |

The last seven rows are the logic of Click `Bool` (Stage 5 of
`design/machine-integers.md`, decision of 2026-10-26), which is the
condition sort: a `Bool` term is a `ConditionTerm`. Besides the literals
(`Constant`), binders (`Variable`) and comparisons it has four value forms
(`src/kernel/primitives/bool_sort.rs`): `BoolApplication`, `BoolIf`,
`BoolEqual` and `BoolLoad`, a one-byte `bool` cell's read. Soundness: L-If
and L-Eq are the two-valued meaning of `if` and of logical equality, and
L-Unfold is the defining equation of a total pure function, whose
termination is checked where it is declared. In the e-graph a `Bool`
value is a class (a literal per value, annotated with its truth; a
binder's class; a call of a function head on its argument classes; a call
of the conditional's head on its three classes; the condition node
`BoolEq`, true when its operands meet; a read head applied to an address
class), so each subterm is interned once and a merge moves truth in
constant work. A binder's facts are kept by binder (`bool_binder_truth`)
until a `Bool` value interns it, so the answer does not depend on which
fact was filed first. The specification lowers `-> Bool` applications to
`BoolApplication`, `Bool` binders to `Variable`, `Bool` conditionals to
`BoolIf` and `Bool` equalities to `BoolEqual`; no front end builds
`BoolLoad` yet (a `bool` cell's read is `byte != 0` over the byte load, so
the load resolutions every other cell read uses apply to it). Every `Bool`
value, in a specification and in C, C++ and Rust alike, travels in a
`ProgramValue::Bool` as its cast to `uint8`, `BoolCast { to: UInt8, value }`, the
byte a `bool` cell holds, and its truth is `value`
(`ConditionTerm::truth_of_bool_word`; a constant word is its own truth). A
C, C++ or Rust `bool` parameter, call result or enum field is a named
`Bool` binder, `ConditionTerm::Variable`; two locals a branch joins apart
become a fresh binder. `if (b)` splits on `b`'s condition, read through its
negations (`ConditionTerm::truth_claim`), and C's `a == b` over two `bool`s
is their logical equality (C1a). A `Bool` binder instantiated with a word
takes that word's truth (substitution of a condition variable, and the
same replacement in the rewriter when a `match` binds one). A `Bool` equality fact is filed under both operands
(`PureFactContext::bool_equation_partners`), so a decided operand decides
the other (L-Eq) in one lookup. Soundness of C1: `b` is two-valued, so its
cast takes exactly the values 1 and 0, which lie in every format.

Rule K7 (decision of 2026-10-26, `design/machine-integers.md`). For `F` of
`b` = 8 or 16 bits, `m = 2^b - 1`, `s = 2^(b-1)`, and `S` of at most 64
bits, with `w = x` up to 32 bits and `w` the low word of `x` (the
`UInt32From64` spelling of `Cast`) at 64: the cast
denotes `n mod 2^b` read in `F` (`n` the operand's value), whose word is the
zero or sign extension of those bits (the narrow-value invariant above). `w`
holds `n mod 2^32`, so its low `b` bits are `n mod 2^b`; `w & m` is their
zero extension, and `(t ^ s) - s` for `t` those bits is `t` below `s` and
`t - 2^b` from `s`, with no 32-bit wrap: their sign extension. Interning a
narrow cast interns this word from the operand's class, at most five nodes
and one merge, so the work is constant per cast and a nested cast is
interned once (`equality_graph/narrow_cast_tests.rs` and its scaling test);
`matrix_tests.rs` checks the word value by value at every narrow format.

The cross-format relations (decision of 2026-10-29,
`design/machine-integers.md`, "Every format its own nodes") are e-graph
facts between nodes of different formats. Soundness: a sign-free operator
computes modulo `2^w`, and reducing to fewer bits is a ring homomorphism
that commutes with the bitwise operators bit by bit (R-dist); every
conversion keeps its operand's low bits, and a widening into a format that
contains its source keeps its value (R-comp); a conversion between the two
formats of one width is a bijection (R0). A narrow operand's word is a
canonical carrier only by its producer's range facts, so neither R0 nor an
R-comp that names a narrow operand itself applies at 8 or 16 bits: a
conversion reads only its operand's low bits there (K7), and only a byte
read is inverted, by its own rule. Each fires where a conversion
node meets an operator or conversion node in one class, when either is
interned or a union brings them together. A class keeps one operator per
format and operator, one conversion per kind applied to it and one
conversion per kind it holds, and each pair fires once, from a queue the
closing loop drains one relation at a time, so a firing is at most three
interned nodes and one union, and a chain under a conversion is a loop, not
a recursion (`equality_graph/machine_relations_tests.rs` and its scaling
tests). σ at 32 bits is a node of its own (step 4b), so the rules act on
it as on the 64-bit conversions and on conversions into 8 and 16 bits; σ's
inverse interns its own node, so σ over a chain costs about three times
the 64-bit reinterpretation per operation, whose inverse is the word itself
(`sign_cast32_distribution_is_linear_in_the_operation_chain`).

Rule N (decision of 2026-11-02, `design/machine-integers.md`) relates a
native 8- or 16-bit operator to C's promoted spelling of it. Soundness: a
widening keeps its operand's value, so `widen(a) op widen(b)` computed
modulo `2^32` is congruent to `a op b` modulo `2^N`, and the narrowing reads
exactly those low bits (R-dist read in reverse, with R-comp); a left shift
by `c` below 32 is multiplication by `2^c`, and at or above the narrow width
both sides are 0. Cost: it fires from the same queue as R-dist, once per
operator, and only where it is needed: when the operator's class gets a
32-bit widening, the case R-dist cannot reach (the widened native value
meeting a masked word), and for a shift. C's promoted arithmetic meets a
native operator through R-dist and R-comp alone. An operator R-dist built
is already a narrowing and is skipped, and R-dist of the rule's own
narrowing over its word is marked fired, since it would only rebuild the
operator: without these, each firing respelled the word over fresh
narrowings without end, and fired eagerly a bare chain of native sums cost
about 30 times the work of interning it
(`equality_graph/machine_relations_tests.rs` and its scaling tests;
`narrow_tests.rs` bounds a bare chain's work per node).

Conditions carry their format (`Compare`, `Overflows`), but the term arena
still spells each width with its own operator nodes, so one file,
`machine_integer/representation.rs`, maps a format and an operation,
comparison or overflow test to its node, and a node back to its format and
operation. It is the only place a rule's width dispatch lives. Where a
format has no node the rule is unavailable there: no 128-bit operators and
no narrow quotient (C computes it on promoted `int` words). Those are
representation gaps that Stage 3 of the design removes.

Three choices keep each fact's spelling where the kernel's reasoning reads
it:

- **A `uint32` order is native.** The difference graph gives a 32-bit word
  a `UInt32` node beside its `Int32` one, paired so that a known sign of
  the signed reading, or an unsigned reading on one side of `2^31`, links
  the two (`difference_graph.rs`, `readings`); the fact context files
  `uint32` orders in their own endpoint index (`uint32_order_bounds`) and
  in the format-indexed order walk (`WIDE_ORDER_FORMATS`), as it files
  `uint64` ones. The condition checker's `uint32` rules
  (`decide_unsigned32_order`) read only those indexes and the graph.
- **128-bit comparisons are spelled as Integers.** `Compare` at `int128`
  and `uint128` folds on constants and reads back as the Integer
  comparison (`integer_observations_of_native_comparison`), but
  `native_comparison_of_integer_observation` leaves an Integer comparison
  of 128-bit observations in Integer form
  (`representation::spells_comparison_natively`): the difference graph and
  interval bounds have no 128-bit nodes and decide it as Integers.
- **Definedness is filed where C's overflow is undefined.** Every format
  has an overflow test, which folds on constants by the exact result's
  range, and `integer_bounds_of_definedness` reads it at any format. The
  fact context files a definedness fact beside its two Integer bounds only
  at `int32` and `int64` (`representation::files_definedness`). An
  unsigned test is a wrap and kernel-internal: surface `defined(...)` is
  about undefined behavior only (`design/machine-integers.md`,
  "Decisions", 2026-10-24). The test matrix
(`machine_integer/matrix_tests.rs`) runs every rule at every format, checks on
constants that it decides as exact arithmetic does wherever the values fit,
and names each gap; a rule that misses a format, or newly reaches one, fails
it.

Two statements reach formats or operations they did not before, and each is
a kernel trust the certificate checkers apply:

- **Product identity.** `integer_operation_identity` accepts a machine `*`
  at every format with a product node (8 to 64 bits), as it accepts `+` and
  `-`. A machine product is the product of the operands' words modulo
  `2^w`, the word's width. Each operand's word is congruent to its value
  modulo `2^w`: a 32- or 64-bit word is its value's bits, and a narrow word is
  its canonical extension, congruent modulo `2^32`. Multiplication respects
  the congruence, so the machine result is congruent to the exact product.
  The two certified bounds put the exact product inside `F`, where it is the
  one element of its residue class, and for a narrow format inside the
  word's canonical range, so the word is that product's canonical carrier.
  This is the argument the rule already relied on for `+` and `-`.
- **Signed operation bounds.** `operation_bound` gives bounds for `int32`
  and `int64` quotients, arithmetic right shifts and remainders by a
  constant, read at the format: the word `0xfffffff8` is `-8`, which gives
  nothing. For `q = x / c` with `c > 0`, C's quotient truncates toward zero
  and `r = x - c * q` has the sign of `x` with `|r| <= c - 1`, so `c * q -
  (c - 1) <= x <= c * q + (c - 1)` and `-(c - 1) <= r <= c - 1`. With
  `c > 0` neither division by zero nor `MIN / -1` arises, so the quotient is
  defined. An arithmetic shift by `k` below the width is the floor of
  `x / 2^k`, which has the unsigned form `2^k * q <= x <= 2^k * q + (2^k - 1)`.

The modular rule is stated at every width, but the fact context files it at
32 bits only, as before. A narrow format's operations are 32-bit word
operations, which do not reduce modulo its own width, so `wrapped_equality_at`
refuses a narrow modulus.

## C ABI and memory layout

The C front end models one explicit ABI: LP64. In that ABI, `int8` has size and alignment 1, `int16` and
`uint16` have size and alignment 2, `int32` has size and alignment 4, `uint8`
has size and alignment 1, `uint32` has size and alignment 4, `int64` and
`uint64` have size and alignment 8, and every supported pointer has size and
alignment 8. Struct fields are aligned individually and the
struct size includes the tail padding required by its maximum field alignment.
Named enum fields use the supported four-byte `int32` representation. The C
metadata retains the enum declaration and enumerator values, but lowering
turns an enumerator into its int32 bit pattern and emits the same scalar field
load or store as an `int32` field. The same representation is retained when a
supported struct value is copied by value. Inline scalar-array fields are
copied one element at a time rather than loaded as aggregate `ProgramValue`s.
For example, `{ uint8 buf[16]; int32 a; int32* p; }` places `buf` at byte
offset 0, `a` at byte offset 16, and `p` at byte offset 24, and has size 32.
Inline scalar arrays are retained as aggregate type metadata, but an array
field used in an expression decays to a pointer to its first element; the
kernel never represents the aggregate as a runtime `ProgramValue`. Embedded struct
fields follow the same address-first rule: for `{ uint8 tag; struct inner in;
int32 tail; }` with `inner` sized at 8 bytes, `in` starts at byte offset 4 and
`tail` starts at byte offset 12. The Click's C front end carries `in` as an aggregate
place while nested member lowering adds the inner field offset before emitting
the kernel's scalar load or store. Taking the address of a modeled scalar leaf
uses that same typed lvalue path, so the pointer retains the allocation block
and the combined ABI offset rather than materializing an aggregate value.
Direct whole-struct lvalue loads and copies are lowered into typed leaf loads
and stores using the same address-backed layout; the kernel still never
represents a struct as a runtime `ProgramValue`. Resource clauses may name embedded
aggregates directly and expand into typed leaf ranges while preserving their
field metadata. Memory coverage, splitting, and joining are decided bytewise: a
pair is re-spelled into one element width, or compared as byte footprints when
the bounds do not divide. An enclosing owned object can therefore be lent to
satisfy a leaf-width view, and two owners of the same bytes at different widths
are refused as overlapping. Typed loads and stores keep their own widths. Fixed
multidimensional arrays of embedded structs and supported scalar fields retain
their declared shapes in Click's C metadata. Indexed leaf access flattens indices in
row-major order before adding the nested struct's complete ABI stride or the
scalar field's element-width stride.
Taking the address of an indexed scalar-array cell uses the same typed lvalue
path, so the resulting pointer retains the containing allocation and points at
the flattened cell rather than at an aggregate temporary.

Copyable by-value structs are the first exception to that address-first
boundary. Click retains each leaf field name, byte offset, and kernel type in a
flattened `AggregateLayout`; embedded fields use qualified names such as
`inner.value`. The kernel binds a value to an `AggregateObject` with its own
local block. Each automatic aggregate declaration owns its complete byte range,
including ordinary C record locals as well as construction destinations. This
lets a modular pointer result use the existing address equality and resource
coverage rules to access the caller's record; ownership alone does not
initialize its fields or establish an alias. Parameter binding, local
assignment, and aggregate return materialization allocate fresh blocks and recursively copy the modeled scalar,
array, fixed-dimensional embedded-struct-array leaf, and data-pointer fields.
Multidimensional embedded-struct arrays are expanded in declared row-major
order, so each nested leaf retains its complete element stride. Pointer fields are
shallow copies of typed
eight-byte pointer values: the destination aggregate gets the same pointer
provenance, not a duplicate pointee allocation or ownership transfer. The
aggregate still has no runtime `ProgramValue`: expressions decay to its address for
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
small ABI boundary: Click's struct-pointer view is `int32*`, while the internal
address-backed return slot is `uint8*`. The return transition accepts only
those two modeled data-pointer views, retags the address at that boundary, and
copies every modeled leaf into a fresh `__return` block. Consequently a
postcondition such as `result.inner.flag == source.inner.flag` compares the
fresh result cell with the source state without turning the returned
aggregate into an alias or weakening ordinary pointer-return type checks.

Positional initializers for copyable struct-valued locals use the same
address-backed boundary. The C parser walks fields in declaration order,
recurses through explicitly braced embedded structs and embedded-struct
arrays, and emits typed stores for each initialized leaf. It emits explicit
zero stores for omitted members and cells, so an automatic aggregate is fully
initialized before later field loads. Designated initializers and struct-array
initializers remain outside this slice; no runtime aggregate value or padding
store is introduced.

Field lowering retains these byte offsets as `ProgramExpression::PointerOffsetBytes`;
it must not encode a struct offset by pretending that a struct pointer is an
`int32*`. Tests compare mixed scalar/pointer layouts against Rust `repr(C)` on
the supported LP64 host ABI.

### Index and offset arithmetic

Two number systems meet in every memory rule, and confusing them is a
soundness bug rather than an imprecision.

Before either of them: **`MachineTerm::as_const` answers `u32`, and every
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
facts, and nothing else may be asked in its place. The hop is a keyed lookup
in `exact_constant_equalities`, which files each true equality with a
constant side under its other side, not a scan of the condition facts.
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
would close nothing. Adding two quantities with the modular `MachineTerm::add`
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
merge and leaves both facts in the state, a published `count >= visible`
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
never wraps. An **element index** is modular. `MachineTerm` is a 32-bit
machine value, so `MachineTerm::add` and `MachineTerm::subtract` wrap:
`i + 1` is the successor of `i` only while that add does not carry out, and at
`i == i32::MAX` it is `i32::MIN`.

The two meet in `element_index_from_offset`, which divides a byte offset by an
element width and folds the pieces with the *modular* add. What it returns is
therefore the element delta only **modulo `2^32`**, and the same is true of
`Pointer::element_index_from_base_with_width` and of every endpoint a rule
builds with `MachineTerm::add(base_index, range.start())`. So is
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

A stated `separate(memory(...), ...)` lowers structurally to `ResourceSeparate`.
It neither adds extent facts nor generates extent obligations. Ordinary operand
expressions retain their evaluation prerequisites, such as signed overflow.
Physical access and ownership admission still require their own bounds.

Preservation interprets only complete physical observations: its memory route
uses constant signed endpoints, their nonnegative difference, and checked byte
scaling. It never treats a wrapped byte count as evidence for a scalar cell.
Symbolic ranges require an explicit restriction to a complete cell first.
This applies to value and definedness preservation and the explicit-write form.

## Floating-point semantic boundary

The kernel models `float` and `double` as typed IEEE-754 payloads in `ProgramType`
and `ProgramValue`. Slices 1 through 5 carry those payloads through parameters, locals,
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

Named unions are represented on the C side as address-backed layouts. Every
modeled member has offset zero, and a member read lowers to a kernel typed load
using that member's scalar or pointer type. The kernel still has no runtime
union value or active-member tag; Click therefore rejects union writes and
whole-union operations, while the tag/member relationship remains an explicit
source-level precondition or branch.

This is not a target-independent C model. Packed structs,
non-LP64 targets, and field types outside documented supported C are not
silently approximated; they must remain unsupported until their ABI rules are
represented explicitly. Bitfields and other compiler-dependent layout rules
are tracked in `roadmap/multiple-compilers.md`.

Untyped pointer operations likewise do not infer an `int32` pointee. An
untyped load, index, or pointer addition whose pointee type cannot be recovered
produces `RuntimeError::IndeterminatePointeeType`. Importers should normally
emit typed loads/stores and preserve enough pointer-type information to avoid
that model error.

## Symbolic execution

### What stepping a statement means

Click never runs code. Stepping a statement records what the statement means
in four parts, on each path it opens:

1. **Terms for its values.** Each operand becomes a term at the current state:
   a variable's current value, a read `load(retained_state, address)` at the
   state it reads (a proof spells it `at(point, e)`), or arithmetic,
   comparison and pure-function application over other terms.
2. **Facts.** Equalities and other facts join the path's fact context: the
   assignment `x = e` adds `x == <term of e>` to the e-graph, and operations
   add their side facts, such as a narrow value's range.
3. **Obligations.** What the statement owes: no undefined behavior (overflow,
   out-of-bounds or unviewable reads, division by zero) and each callee's
   `requires`.
4. **Memory and resources.** The one part that is not facts: what is stored
   where, and what is owned, viewed or lent. Stores, declarations, scope ends
   and calls change it; arithmetic and reads do not.

A condition whose value the facts do not decide splits the path, once per
truth value, and each side gains the condition or its negation as a fact.
`prove_symbolic_program_condition_evaluation` is that rule for a control-flow
condition; tactics use it to select `if` edges.

A call is one more part of an expression, not a separate mode. Proofs
execute under `ExecutionSemantics::APPLY_VERIFIED_RULES` (below), so a call
applies its callee's contract and never its body. It owes the `requires`;
its result is a fresh symbol, which a proof names by its site,
`statement(i).call(f, j).result`; the `ensures` become facts about that
symbol and the arguments; and memory and resources become what the contract
says the call leaves. The result is not the term `f(args)`: the contract may
leave it open or depend on memory, so two calls with equal arguments are not
known to agree. Only a pure function's application is a term, equal for
equal arguments by congruence.

So `int x = foo(bar(y));` steps as:

```text
r1 := statement(i).call(bar, 0).result   owes bar's requires on y; facts: bar's ensures
r2 := statement(i).call(foo, 0).result   owes foo's requires on r1; facts: foo's ensures
x == r2                                  memory and resources: bar's effects, then foo's
```

A loop is a cycle through named points: its head (`loop(i).entry` before the
first pass), the statements of its own that run before its test, its test, its
body, its back edge and its exit (`loop(i).exit`). A pure condition such as
`k > 0` is tested at the head, so the body starts with it as a fact and the
exit with its negation. A condition that calls a function makes those calls
its loop's own regions (`loop(i).call(f, j)`), followed by a test region
(`loop(i).test()`, the kernel's `ProgramStatement::LoopTest`): a pass steps the calls
and then the test, whose true side continues the pass and whose false side
leaves the loop there, marked `LoopControlExit::TestFalse` on the frontier.
The other loop forms place statements differently around the same points: a
`do ... while` runs its body before the test, and a `for` its step at the back
edge. After a loop that left on one path, the points of that path's last pass
keep their names (its calls, `.result`s, test and body statements); after a
loop that left on several, those names are refused, since each path recorded
them at its own state.

An expression's effects are steps of their own, run just before the
statement that holds the expression:

- A call is `ProgramStatement::CallResult`. The surface spells its result by
  its call, `statement(i).call(f, j).result`. The result has the callee's
  declared type.
- An assignment inside an expression, or a `++x` or `--x`, is a
  `ProgramStatement::Assign`. The expression then reads the local.
- A postfix `x++` or `x--` is a `ProgramStatement::Assign` with `prior_result`,
  which keeps the value it replaces. The surface spells that value
  `at(<the assignment's region>.entry, x)`.
- A `&&`, `||` or ternary operator whose operands make steps is a
  `ProgramStatement::If` that decides which operand runs, and each arm ends in
  a `ProgramStatement::StepValue` that records the operator's value on that
  path. The surface names the decision `S.and(j)`, `S.or(j)` or
  `S.ternary(j)` and its value `.result`. In a condition such as
  `if (a() && b())`, the statement's own `if` then reads that value, which each
  path has already decided.

- A statement expression `({ body; value })` runs its body, then a
  `ProgramStatement::StepValue` records its value. `WRITE_ONCE(x, v)` records
  `v` once under two steps, one read by the ordered store and one by the
  expression. A discarded expression statement is a `StepValue` with no steps:
  its value is evaluated and discarded.
- A call through a function pointer is a call whose `callee` is the pointer
  expression; its `function_name` is the pointer as the source writes it. The
  surface names any call `S.call(j)`, counting every call of the statement, and
  a call of a named function also `S.call(f, j)`.

A step's result stays in the path state by its number
(`ExecutionState::step_results`), and the statement reads it as
`ProgramExpression::StepResult`. Each result ends with the statement that
reads it, or with the condition that decides a branch.

#### Where the implementation departs from this

The Rust importer gives every MIR local the user did not name a local
`__rust_mir_<N>` (`src/languages/rust/charon.rs`). MIR is three-address code,
so most of these hold one operand of a larger source expression.

`src/languages/rust/charon/temporaries.rs` puts a pure value back into the
expression that reads it. To move, the temporary must:

- be unnamed;
- be assigned once, from a value with no effect;
- be read once, later in the same block, with nothing between the two but
  storage markers, assertions and other such definitions.

`x = a + b * c` is then one expression again.

A value with a checked operator (`+ - * / % << >>`) moves only into a read
whose lowering emits that operator's panic check:

- an assignment's value;
- an assertion;
- a call argument;
- an index;
- an operand of an operator or conversion in one of these.

At any other read, it stays a temporary: an enum constructor's field, a branch
condition, a `match` scrutinee. Moving it there would drop the check.

A call whose result one later expression reads, in the call's only
successor, is a call step (`temporaries::call_steps`): the MIR call carries
the step number in `result`, the read is `Expression::CallResult`, and the
lowering emits `ProgramStatement::CallResult`. A proof names its result
`call(f, j).result`, among the function's calls.

These still stay a temporary:

- a call's result read more than once, so a `for` loop's `next` result is one
  and a proof sees it;
- a borrow;
- an indexed place or slice;
- a local that roots a place (`&t`, `t.f`, `t[i]`);
- an enum `match` scrutinee, whose proof split names a local.

This temporary is a defect to remove, not a design to extend. A proof should
never see `__rust_mir_<N>` or any other name a front end or compiler invented. Do not add a temporary, a name check, or a special case
that depends on one; where existing code needs one, remove it by moving toward
the model: a call is a node of the expression that holds it, its result is
named by its site, and no compiler temporary becomes a program variable.

### Paths and outcomes

The symbolic executor produces execution paths. Each path includes
execution-derived pure facts (public or private), proof obligations, and an
outcome theorem. The function-specification prover checks that every path
satisfies the function contract and that its remaining facts and obligations
are justified by requirements and proof machinery.

`prove_program_function_satisfies_specification_from_symbolic_path` accepts only
the exact function, entry state, arguments and outcome recorded in the
certified path; it does not turn arbitrary outcomes into theorems.
`program_function_execution_candidates_from_outcomes` constructs no theorem.
Budget exhaustion is an `ExecutionLimit`: a proof or executor failure, not C
undefined behavior.

### Fresh identities

One symbolic execution has exactly one fresh-identity counter, on its
`ExecutionBudget`. A loop head's havoc of modified locals, a re-bound
binder's model fields, an opaque call result, a heap allocation, an aggregate
field and a join's abstraction all draw from it, so no two of them share an
identity. Reserved-set probing narrows what one stream issues; it is not what
keeps allocators apart. Fresh reservations include the free Integer
identities inside every specification application argument, whatever the
result sort, while execution-memory states stay opaque (regressions in
`src/kernel/tests/execution_tests.rs`).

- **A rule that abstracts a state takes the counter and returns where it
  left it.** `abstract_execution_state_for_join` and its siblings take the maximum of
  the arms' counters, since the arms' abstractions are compared for equality,
  and return a `StateJoinAbstraction` pairing the state with that mark, so a
  caller cannot keep the old counter. A loop head's
  `LoopPreservationContext` reports its mark the same way; both the
  continuing iteration and the body proof start from it.
- **The counter only moves forward, and only the kernel moves it.**
  `ExecutionProofCore::next_kernel_variable` is private; callers read
  `kernel_variable_mark` and change it only through
  `advance_kernel_variable_mark`, which refuses a lower mark. A rewound
  counter would re-issue identities still in use, a false-theorem hazard.
  Where a join invents identities, the kernel installs the mark of the
  abstraction it recomputed (`ExecutionProofCore::record_interface_branch_join`).
- **Every budget says how it starts; there is no default.**
  `ExecutionBudget::for_new_execution` starts at `KERNEL_VARIABLE_BASE` and is
  legitimate only where no live state carries issued identities: an
  execution over a state the caller built, whole-function contract
  certification, a refinement context built from two contract interfaces.
  `ExecutionBudget::continuing_from` counts up from a mark an execution has
  reached. Work allowances (`with_program_expression_cost` and its siblings) are
  builder steps on either.
- **`ExecutionBudget::beside_live_state` cannot invent an execution identity
  at all.** Its users are the proof-side families reached from `have`,
  `fold`, `unfold` and theorem application: fixed-state spec lowering and
  capture, composite-resource proposition evaluators, instance fold and
  unfold rewrites, arm-premise and witness binders, the loop invariant and
  effect obligation APIs, and independent contract certification. They do not
  carry the execution's mark, so `allocate_kernel_variable` refuses with
  `ExecutionLimit::ExecutionIdentityBesideLiveState` ("internal: execution
  identity requested beside a live state"). A site that needs an identity must
  be given the mark and use `continuing_from`.

Match-arm binders do not need the execution counter: they are *bound*
variables of the lowered term, drawn from
`ExecutionBudget::MATCH_BINDER_VARIABLE_BASE` by a counter the budget owns,
so nested matches get distinct binders and no binder equals a free identity.
Separately lowered terms reuse binder identities safely because `TermRewrite`
alpha-renames a binder that would capture and stops under a shadowing one.
`rewrite_integer_match_typed_fields` receives an arm body without its `Match`,
so it checks that every identity it substitutes satisfies
`ExecutionBudget::is_match_binder_variable`
(`mdtests/match_binder_captures_havocked_local.md`). Case witnesses are
different: the fields of an undecided `algebraic_case_paths_in` split are
*free* variables of the constructor equation it publishes, so they come from
the execution counter and refuse beside a live state. A variant test
`x is V` beside a live state therefore splits nothing: it lowers to `x == V`
for a variant without fields, or to `x != W` for each other variant when
none of them has fields (`enum_is_without_witnesses`).

The mark is execution-relative — an offset from `KERNEL_VARIABLE_BASE`, which
is the representation `ExecutionBudget::continuing_from` takes and
`ExecutionBudget::next_kernel_variable` returns. A freshness probe that
compares a candidate `Variable` against it must add the base back:
`ExecutionProofCore::issued_kernel_variable_bound` closes the range
`KERNEL_VARIABLE_BASE .. bound` holding everything this execution has issued.

The counter runs from `ExecutionBudget::KERNEL_VARIABLE_BASE` and refuses
with `ExecutionLimit::KernelVariables` at `KERNEL_VARIABLE_CEILING`, the lowest
base another producer reserves, one comparison per allocation. Each producer
stays within its own range:

| Range | Producer |
| --- | --- |
| `1_000_000 .. 2_000_000` | the execution's fresh-identity counter |
| `2_000_000 .. 4_000_000` | the surface's quantifier variables; lowering refuses at the ceiling |
| `4_000_000 .. 4_000_000_000`, stepping by `65_536` | the surface's algebraic binders; lowering refuses at the ceiling |
| `4_000_000_000 .. 8_000_000_000` | symbolic pointer blocks |
| `1 << 40 .. 1 << 41` | load variables (`LOAD_VARIABLE_BASE`) |
| `1 << 41 .. 1 << 42` | match-arm binders (`MATCH_BINDER_VARIABLE_BASE`) |
| `1 << 42 .. 1 << 43` | universal-introduction witnesses (`UNIVERSAL_WITNESS_VARIABLE_BASE`) |
| `1 << 43 .. 1 << 44` | spec fold binders (`spec_fold_bound_variable`, base plus hash) |

An execution allocates in its range (`KERNEL_VARIABLE_BASE` up to
`KERNEL_VARIABLE_CEILING`) from its budget's counter and must not hand out a
number its inputs already name. It reserves the variables of the state, the
statement or call and the environment by collecting them. Its fact context's
variables are reserved by a bound instead: `PureFactContext` keeps an upper
bound on the execution-range variables its facts mention
(`ExecutionVariableCeiling`), and the counter skips past it. Filing a fact
reads only its syntax; a fact that names a memory state is queued and taken
whole, the state's variables included, the first time an execution asks,
so asking at every call costs what was filed since the last call.

Direct contract `forall` certification introduces its witness through
`Variable::allocate_fresh`, whose private identity origin and process-wide
counter mean `Variable(n)` cannot forge its result. New kernel rules that need
an arbitrary fresh variable use this allocator rather than another range.

The match-binder and spec-fold-binder ranges carry soundness obligations:
a binder that equals an unrelated free identity can capture it. The
`the_match_binder_range_is_disjoint_from_every_other_producer` and
`the_spec_fold_binder_range_is_disjoint_from_every_other_producer` tests assert
their boundaries. Match lowering refuses with
`ExecutionLimit::MatchBinderVariables` if it exhausts its range. Arm refutations
start at `1 << 56`, and structural induction starts at `1 << 60`, above the
fold range.

The witness range carries the same obligation. `intro` on `forall v. body`
replaces `v` by a free identity that must name nothing the state names,
including program variables, the store, the memory state and resources,
not only the facts; so it comes from its own range rather than from the
facts' unused identities
(`the_universal_witness_range_is_disjoint_from_every_other_producer`,
`a_freshened_universal_witness_never_takes_a_program_identity`). A proof that
exhausts it refuses rather than reusing an identity.

Freshening a binder is a renaming, so it must not change what the proposition
says *or how it is spelled*: a proof state matches a goal against a fact
syntactically, and a goal that quietly moves to another canonical form stops
matching the surface's re-lowering of the same written range. That is why a
range's byte extent has exactly one constructor — `memory_range_byte_count`
folds through `MachineTerm::subtract`, the same one substitution rebuilds
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

The kernel has no statement that stands for a block — Click lowers a source block
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
state still names its final index for proof provenance; the subsequent
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
selected entry state. Materialized aggregate results belong to the caller
and survive the callee's exit.

The contract return value uses an internal binding that no C identifier can
spell. Bare `result` lowers to it, while `c(result)` resolves the source C
binding, including inside casts, field projections, and array indices.
Kernel post-state reconstruction and fixed-state proof lowering use
that separate return binding, preserving a same-named parameter's value.

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
than only their starting addresses. The implicit empty-footprint check uses the
path's equality facts to recognize writes through symbolic pointers to
preexisting heap or named storage, in both exact-write and effect-range facts.
Resolving a load to a stored scalar requires
the load's recorded width to match the stored value; a width-less term cannot
choose a cell type implicitly.

Call and loop behavior are explicit inputs to kernel execution. The common
configurations are:

- `ExecutionSemantics::EXECUTE_BODIES` evaluates callee bodies, verifies
  annotated loops directly, and ignores available verified rules. Low-level C
  evaluator tests use this mode.
- `ExecutionSemantics::APPLY_VERIFIED_RULES` applies opaque function and loop
  rules and never evaluates the corresponding bodies. Click execution proofs
  use this mode.

`ExecutionEnvironment` contains the function definitions and verified rules
available to an execution; it does not select between these semantics. In
particular, rule lookup is not a fallback mechanism. Applying verified rules
without a matching rule fails, while direct body verification behaves the same
whether or not a matching rule is present. `ExecutionSemantics` also exposes
`APPLY_CALL_RULES_AND_VERIFY_LOOPS` for the loop-rule construction phase,
where calls remain modular while the current loop body is verified directly.

Concrete execution judgments and modular verification transitions are
deliberately different propositions. `ProgramStatementExecutes` and
`ProgramFunctionExecutes` describe outcomes produced by direct operational
execution. `ProgramStatementVerifies` and `ProgramFunctionVerifies` describe abstract
branches admitted while checking partial correctness with loop or function
summaries. A verification return branch means “if this computation returns,
this is an allowed post-state”; it is not evidence that the return is
reachable. Verified contract and loop rules cannot be converted into concrete
execution or termination theorems.

One driver steps statements and functions for both judgments
(`execute_statement_paths` in `src/kernel/eval/statements.rs`, and
`execute_function_body_paths` and `execute_function_paths` in
`src/kernel/functions.rs`). The judgment is its parameter
(`StatementJudgment`), and every statement a judgment contains, in a sequence,
a branch, a loop body, a switch case or a handler, is stepped under the same
judgment. The judgments differ in exactly two named branches:

- a loop: under verification, an environment's verified loop rule, or the
  loop's own invariant, effect and termination checks, step it as its checked
  abstraction (`abstract_loop_paths`); execution, and verification of a loop
  with neither, unroll it;
- a function applied as a whole: under verification, a function that declares
  a measure has its recursion anchor installed before its body runs.

Everything else is shared: each statement is charged one step, every
statement passes the same pending-thread-create gate, and a sequence whose
first statement leaves abnormally carries that statement's facts and loan
evidence out with it. `execute_execution_statement_paths` and
`execute_execution_statement_verification_paths` remain only as names for the two
judgments.

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
records `HeapAllocated` from the pending state and creates a
fresh heap allocation with an exact, possibly symbolic size, marks its cells
uninitialized, and produces complete owned memory plus the
exclusive `allocation(base, bytes)` lifetime resource. Returning a different
value while an allocation outcome remains unresolved is rejected.

An allocation marked `ends_program_on_failure` has no null arm: its failure
ends the program rather than yielding null, as a C++ `new` does in a `noexcept`
function, where `std::bad_alloc` calls `std::terminate`. No execution
continues past a failure, so the transition records the result as not null
and resolves it at once to the success arm. Partial correctness, and
termination, are unaffected: the ended program makes no return.

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
free as `HeapAllocationFreed(before, after, base, bytes)`. Effect
certification checks that executing `free(base)` from `before` with the stated
extent produces `after`, and chains that transition separately from ordinary
`MemoryMutatesOnly` and ranged call-havoc effects. This lets a function free
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
base context. Remaining requirements belong to proof obligations and must be
discharged before contract completion; legacy contract-path preparation still
performs part of this work. These evaluation orders are logically neutral, but prevent ordinary
verified-call chains from repeatedly scanning every earlier call fact.

Smart execution and exact certification share the same bounded order
derivations. In particular, a strict upper bound justifies the non-wrapping
step from `x` to `x + 1` even when the two `x` loads use memory states
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

`MachineTerm::RangeFold` is the symbolic representation for pure Click
folds with symbolic bounds. The constructor performs basic simplification:

- equal start/end -> initial value
- one-step range -> substitute once
- small concrete ranges -> unroll

Additional equality logic recognizes count-shaped folds and sum commutativity
for the standard-library `count`/`permutation` proofs.

## Click lowering

`src/surface/lowering/` has several lowering/evaluation paths because contracts are
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

The Click parser is hand-written in `src/surface/parser.rs` and
`src/surface/parser/`. Validation in `src/surface/validation/` checks:

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
match. The ordinary one-step pure-function elaborator then exposes
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
among the requirements and must rewrite the goal in the listed order.
