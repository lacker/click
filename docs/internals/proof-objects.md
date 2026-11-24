# Proof objects

Click's kernel `ProofObject` is the persistent semantic representation of an
evolving proof. The language-layer `Proof` wrapper pairs that opaque handle
with source context and proof lineage. Together they let explicit tactics
and smart search share one checked-transition boundary while keeping semantic
authority separate from the record used to explain or expand the result.

The [proof operations/search split](https://github.com/clicklang/click/blob/master/design/proof-operations-and-search.md)
separates explicit operations from the `kernel::search::ProofSearch` discovery
interface over the same persistent state. A frozen reference inventory records
remaining operation-to-search calls; this is not yet a complete efficiency boundary.

## Persistent proof state

The kernel `ProofObject` owns an immutable `ProofState` and the focused branch
cursor into that state. The language-layer `Proof` wrapper pairs that opaque
handle with a shared checking context and Surface lineage `ProofNode`.
Applying a checked operation returns a successor that shares unchanged
structure with its ancestor. A smart tactic can therefore branch, inspect
alternatives, and abandon candidates without cloning the complete logical or
execution state.

The kernel owns branch and split identities and the persistent open-branch
topology in `src/kernel/proof/branches.rs`. Its
surface-independent persistent containers already live in
`src/kernel/proof/storage.rs`, while typed execution-frontier state lives in
`src/kernel/proof/execution.rs`. That module now owns the complete
surface-independent `ExecutionProofCore`, not only its frontier. The persistent
fact store's structural keys live in `src/kernel/proof/fact_keys.rs`. The fact store's semantic matching,
transport, conflict, and state-equivalence rules live beside those keys in
`src/kernel/proof/fact_reasoning.rs`; Surface Click fact selection, diagnostic
rendering, and budgeted smart premise search remain in the language layer.
`PureFactStore` and all of its persistent semantic indexes live in
`src/kernel/proof/facts.rs`; language code receives an opaque store and uses
named queries and persistent successor operations rather than its fields.
Kernel `ProofObject`, `ProofState`, `ProofBranch`, and `ProofBranchState` own
the persistent handle, state, focus, and open-branch shapes. Surface-local
names, obligation presentation, and execution presentation are opaque type
parameters; the kernel containers never inspect them or accept them as
evidence. The proposition/frontier/outcome obligation enum,
effect selections, result-aware outcome state, and checked frame authority
live in `src/kernel/proof/obligations.rs`; proposition and outcome presentation
are opaque parameters. Goal-preserving fact or execution updates, strict
frontier updates, obligation replacement, and conditional discharge are
implemented on the kernel branch store rather than in the Click proof driver.
The kernel handle is also the sole constructor of completion witnesses and of
the typed finalization view proving that the focused obligation is an
execution frontier at function exit. Primitive proposition operations check
availability and logical shape, refine or close the obligation, and return an
opaque successor directly. `intro` accepts a callback only to derive new
opaque presentation from the checked introduction kind; the callback cannot
choose the kernel proposition, introduced fact, or successor state.
Explicit implication application and universal instantiation likewise accept
lowered inputs, then let the kernel establish availability and guards before
it constructs and publishes the resulting fact.
The raw persistent fact insertion and focused-state replacement operations are
scoped to `src/kernel`; their `with_kernel_checked_fact` and
`publish_checked_result` language adapters are carry-only seams for results
already produced by operation-specific checked kernel drivers. They do not
derive or bless propositions themselves, so keeping raw callers inside the
kernel is an explicit trusted boundary guarded by a source-scope regression.
For proposition `if` and `cases`, the kernel allocates the audited split and
sibling identities, checks complementary or available case facts, and owns the
closed-arm join. Surface lineage independently proves that serialized arm
steps descend through the exact split marker; it never manufactures branch
state. A source `cases` may establish its disjunction through an ordinary
nested `have` before the split. The driver uses the ordinary implicit closer,
and expansion retains the explicit checked proof before either arm. Deferred
post-execution splits retain these proofs by source occurrence on each outcome;
preceding explicit `have` steps are checked in source order and their certificates
are reused during final assembly. Already justified complementary splits retain
the kernel's direct evidence. Logical `cases` at an execution frontier uses the same operation while
sharing the unchanged execution core between both fact-local siblings. For a
proof-level execution `if`, the language prepares each arm's opaque Surface
record, while the kernel validates polarity and attaches those records to its
own clones of the unchanged semantic core. Presentation-only proof marks use a
kernel operation that cannot replace the execution core, while loop invariant
closure is a named semantic-core update checked by the kernel.
Fresh language proof contexts supply an unproved root obligation to the kernel
root constructor instead of assembling a complete `ProofState`. Re-focusing a
checked arm is a kernel-validated cursor move that rejects retired, reserved,
or unknown branch identities and may replace only its reported fact delta;
production language code has no generic whole-handle state-replacement
operation. Metadata capture consumes a frontier handle through a separate
kernel operation that exposes only the opaque Surface presentation attachment;
the callback cannot mutate the checked execution core or branch state.
Ordered post-execution scheduling records are presentation methods as well;
recording one does not expose or rebuild the semantic frontier.
Region-level smart-closer attribution and the final construction cursor for
smart step/execute are stored and updated through the same presentation-only
path. The semantic core retains only the checked invariant-closure flag.
Statement steps, mid-execution `have`, frontier-local `loop`, and resource
scope entry/closure submit their checked successors through a frontier-shaped
kernel operation that preserves unrelated branches, the obligation, and unfold
state. Terminal branch-arm continuation uses the same operation.
Loop initialization obtains exact entry judgments and introduction metadata
from the kernel, indexed by invariant declaration even when a goal is already
satisfied. One fixed-state proof retains the helper steps and checked invariant
scopes. Each source body contributes its own completion and certificate; a kernel
implication rule can restore the leading guards removed at selection without
changing that completion's root assumptions. Initialization never checks the
serialized body to recover its result. Expanded Surface proofs are still
verified independently. Frontier clause binding replaces an earlier registration
for the same C loop identity while preserving the current proof-local scope.

Wide generated invariant bundles use balanced conjunctions, keeping all members
in declaration order while bounding certificate nesting logarithmically. Short
bundles retain their established grouping. Wide source conjunctions can instead
expand to sequential checked `have` leaves followed by `close()`; every
reified leaf must lower to the exact kernel proposition. Neither representation
raises the parser depth limit or skips an invariant obligation.

Simple invariant-bundle preparation retains the already checked path context
between declarations and extends it with each canonical merge's changed facts
and obligations. Replacements preserve the complete source tuple, including
introductions and call-site identity; unresolved mandatory conditions never
become assumptions. Collected goals receive only the changed members, while
entry judgments retain every declaration position, including duplicates.

When loop preservation produces two feasible proof-level `if` arms, the kernel
also allocates the sibling identities and records their split topology around
the two checked frontier results.
Structural C branches may publish only their feasible checked arms; the kernel
reserves the full split identity range and focuses the first feasible sibling.
Post-execution outcome partitions use the corresponding two-arm operation.
At an execution or outcome join, the checked driver supplies the merged
frontier while the kernel validates the child/parent lineage and restores the
retired parent identity.
Post-execution operations advance the focused outcome and its persistent facts
together through checked kernel operations. Retained claim scopes can refresh
resource representation only from their owning outcome; context, outcome identity,
and result must agree. Outcome identity survives a claim scope's local branch IDs. No ambient fact vector is reinstalled.
Function-exit outcome fanout lets the kernel allocate one identity per checked
returning path. A completed `have` scope publishes only its focused obligation,
facts, and optional execution attachment through the kernel.
Pure proofs retain each checked `have`'s written-to-kernel correspondence.
An explicit citation can reuse that correspondence while its program state and
referenced bindings are unchanged. Lookup requires a singleton source mapping
and exact membership of the retained fact; it never scans historical mappings
or grants authority to the written form. Shadowed names, ambiguous mappings, and
missing facts take the ordinary citation-lowering path. New goals and term
construction keep their existing lowering rules.
Structural loop-effect scopes may restore an already allocated retired cursor
for lineage, but cannot invent a branch identity; the kernel also refuses
to retire their frontier until its loop-effect goal is checked closed.
Resource scope close publishes its checked state and fact delta on the
owning frontier or outcome. Outcome closure projects only the restored
composite's observations; unrelated resource facts remain shared. Both
operations preserve the obligation, unfold set, and unrelated branches.
Fixed-state theorem, rewrite, transport, frame, and resource rules use the
same boundary shape: the language checker returns only a focused result, and
the kernel replaces or closes that branch while preserving siblings, topology,
and focus. The kernel's raw `ProofState` fields and `ProofObject` constructor
are private; production language code has read-only state accessors and cannot
assemble or install a whole semantic state.
Result-aware outcome state uses the same split as execution state: the kernel
owns its result, C state, facts, and crossed effects. Source requirement identity
comes from the immutable entry-origin index, independently of subsequently
introduced facts. Surface proposition records and diagnostic metadata remain
an opaque language presentation.
Untrusted smart selection
lives outside `proof_object/` and may inspect its read-only planning interface
or publish descendants created by checked proof operations.
Contextual Surface Click lowering likewise lives beside the language-layer
proof drivers; the checked core retains only the derivation lineage from which
the surface certificate is extracted.

The borrowed parser, project-environment, lowering, and diagnostic inputs are
grouped in `src/surface/proof/language_context.rs`. They are language
context, not persistent proof state. Surface `ProofStep` lineage and checkpoint
extraction are isolated in `proof_object/lineage.rs`; that lineage records
checked successors but does not own semantic state or successor authority.

Goals carry the facts, resources, and symbolic execution state relevant to one
judgment. Typed scope, split, and join helpers preserve branch and loop
structure. A focus is only a cursor into the owned goal structure; it isn't a
second semantic state.

## Source proof and expansion types

`SourceProof` distinguishes an omitted proof, a smart proof request, and an
explicit tactic block. Parsed tactic statements become `ProofTactic` values.
Each tactic has a `TacticClass` used by checking, instrumentation, profiling,
and expansion.

`Proof` lineage retains the surface-expressible operation that produced each
checked successor. `ProofCertificate` is the current structured serialization
of those operations as `ProofStep` values, including nested scopes and
branches. It can be rendered back to surface tactics for expansion. The
serialization carries no semantic authority of its own and need not exist
during ordinary verification in the intended architecture.

A checked decided C split marks its unreachable certificate arm for surface
placement. Suffix assembly skips that arm without traversing each outcome's
branch history. An ordinary empty proof arm remains a live leaf. This private
presentation marker is not rendered as a tactic and does not exempt any
rewritten source from ordinary verification. Expanded C arms with an omitted
sibling use the checked split, validate their explicit entry steps, and defer
outcome operations until function exit. A completed empty C arm rejoins before
its written tail is walked, so these completed splits do not accumulate depth.

No `ProofStep` is smart or internal-only, and both certificate constructors
apply one admission rule: `from_proof_tactics` classifies source tactics and
`from_steps` classifies serialized lineage, so a leaf that no explicit
proof could write is rejected from either direction. A smart tactic therefore
has no step of its own. The implicit back-edge closure of a loop's
`maintain` script, for example, plans the bundle body, and the step retained
for it is the internal `ProofStep::CloseInvariantsBy` carrying that planned
body, which has no Surface form (the `close_invariants` tactic is retired);
the closure request itself is a semantic-core update with no certificate
leaf. Nested certificates are admitted where they
are built, so validating one certificate costs a single pass over its own
steps.

## Execution state inside a proof

Kernel `ExecutionProofCore` owns the semantic execution state for one proof
path: the `ExecutionState`, typed frontier (program point, region, region start state,
and continuations), checked execution facts and loop rules, function-entry
prerequisites and derivations, freshness counters, loop-effect goal, region
flags, structured-branch flags, and unfolded kernel predicates.

Kernel `ProofExecutionState` pairs that core with an opaque language
`ExecutionProofPresentation` containing only Surface Click construction data:
recorded states and their selectors, source text,
case assumptions, frontier loop clauses, planned statement transitions,
branch and outcome evidence, deferred post-execution tactics, and the
`SurfaceRecord` used for certificate extraction. Its `ExpansionCursor` records
where a source tactic's expansion is being captured and holds no semantic
state. Core access is explicit as `execution.core`; the presentation does not
duplicate the C state, frontier, resources, checked facts, or semantic flags.
The checked
drivers no longer mirror surface steps into that builder: a tactic's expansion
and a preservation arm's certificate come from the `Proof` itself
(`certificate`, `certificate_since`, and the lineage-following
`path_certificate` for an unjoined case-split arm), and the certificate
builder is only a planning call's construction sink, owned by the planning
`Proof` method and handed to the executor with the construction environments
as one `Construction` gate. It lives only as the execution
state of a `Proof` goal: the checked drivers advance a `Proof`, and every
source or generated proof tree is checked that way. The earlier interpreter
that advanced this context as a parallel engine is gone; the state owns the
C store and the goal owns the facts.

`ExecutionProofCore` also retains one evidence trace per candidate path:
a persistent sequence of `CheckedExecutionEvent`s. A statement or condition
step records the kernel theorem for its transition followed by the fact
context that theorem was proved under; a proof-level case split records its
arm on every trace it creates and forks the traces with the candidates when
it forks paths after execution; an exhaustive C branch records one nested
node with both arm deltas; a composite `observe`, `fold`, `unfold`, or
scoped open records the resource rewrite. A statement or condition theorem
must prove the source statement the evidence has yet to consume, from the
state the evidence has reached, and the core advances that state and source
from the theorem itself; a record call the proof object refuses fails the
tactic that made it. Recording does not re-validate what the session
produced (`AGENTS.md`, construct valid proofs): a theorem's premises are its
own path facts and obligations beside the recorded context, and are not
looked up again, and a plain composite `fold` or `unfold` is recorded from
the kernel producer's result without re-expanding the definition or
comparing the resource contexts. At function exit
the proof object composes the checked function execution that claim and
contract certification consume (`ExecutionProofCore::checked_function_execution`):
one path per trace, its completing theorem under the contract's exit rule.
It evaluates no C; completion inspects the retained evidence and applies the
checked contract exit rule.

Normalizing a call's facts to the source-statement exit retains each original
execution fact alongside its transported copy. The statement theorem can name
the original state as a premise even for an ordinary, uncertified call
bound. Certification still controls which facts persist as checked effects;
transport does not replace the evidence the statement was checked under.

Named-instance folds after return are persistent, path-indexed trace extensions.
The fold reads the selected trace's completing state, never a sibling's state
or the caller-side postcondition projection. Guarded folds must select the case
justified by that path's retained assumptions. Outcome finishing checks each
modified path, collects its extension by base-trace identity, and publishes one
complete execution after all outcomes are finished. This preserves coverage
without re-certifying every sibling for each fold. Indexing and extending one
path shares the unchanged traces and history.

An instance exchange also retains its checked observation at the published
return state, where automatic locals have ended. Its input must be that
path's publication or the preceding observed exchange's output. Certification
checks the selected resource body at both states and imports only the
semantic facts those exchanges produce, including exact read validity facts.
Before a named output exchange, ordinary composite refolds retain the same
checked return presentation, including wrappers containing only a static owned
range. The next named fold observes that presentation rather than the resources
published before the refold. This uses the existing selected-resource exchange;
it does not rescan unrelated return paths or resource entries. The gate fixture
`static_return_refold_before_named_resource.md` covers the static case.
Post-return unfolds do not materialize additional cached cells: no C statement
follows the return, and naming those loads would change the state used by
claim completion. Unfolds during execution still name their exposed cells.

When a proof matches an already constructed model, an algebraic payload that
already has a Surface variable keeps that identity under the new source name.
The kernel still allocates fresh constructor witnesses and checks the case;
constructor injectivity justifies the retained payload name. The checked
case also publishes its equation under that name. This keeps unfolded scalar
facts attached to the same model value across a fold and another match, without
changing memory states or transferring ownership. Selection reads only the
constructor's requested field, with no search through unrelated premises. Ordinary
resource fold/unfold arguments use these same proof-local bindings, including
when a match binding shadows a C parameter. The dispatcher substitutes only
names in the written arguments and then captures the referenced C locals at
the current frontier before selecting execution or outcome checking. Thus after
`p = q`, both `fold(tag_at(p))` and `unfold(tag_at(p))` name the resource
at `q`; ownership at the entry value of `p` does not suffice. Capture uses indexed
lookups for the written names, without scanning unrelated locals. Storage
operands such as `&x` retain the C place, and explicit program point selectors remain
intact during current-value substitution. Failing population-body folds render
the written resource operand, preserving C names even when checking captured
values. The resource definition, read obligations, and ownership checks remain unchanged. Named-instance
folds continue to resolve their arguments when constructing the instance.

A proof `if` or `match` interface may rejoin before the first C statement.
The kernel first materializes the retained function entry, binding its own
checked arguments without advancing the C source. The arms, abstraction, and
continuation then share this bound state; resuming execution uses the retained
source and does not bind the parameters a second time. Interface clauses still
require checked resources and facts from both arms. Positive pointer equalities
may normalize through the arm's maintained equality graph when a logical read
has a different form; ownership, viewability, and other safety obligations
still need their own checked evidence. Concrete interface clauses are lowered
in that exact arm's maintained fact context, so a wide read through a model
pointer can recover the same cached value used by the arm's explicit proof.
Non-exact condition and read-validity reasoning stays deferred during lowering.
Every lowered fact and safety obligation is still checked separately; lowering
grants no ownership or read validity. The abstract successor retains state-only
lowering so its propositions match the exact exported facts. Both paths share
persistent contexts without rebuilding or scanning their premises.

The kernel interface join constructs successor ownership once: consume the
owned interface from each concrete arm, intersect the residual frames, and
restore the exported interface under the successor facts. The surface supplies
the abstract memory and locals and records the state the operation returns;
it does not construct a second resource exchange for the kernel to compare.
Execution state, retained evidence, and recorded states use that same
constructed successor. Clause lowering reads the common frame and projected
interface models through an unpublished contract view. An arbitrary resource
in a proposed state cannot add ownership to the result.

An interface `branch ensuring` may join different heap lifetimes when the
interface includes an owned, arm-sensitive resource that represents the
lifetime. The kernel's interface abstraction retains the union of potential
live allocations, keeps a tombstone only when every arm agrees that the
allocation is retired, and forgets branch-local cell values behind a memory
history barrier. It then checks that the exported resource expands to the
allocation on the retaining arm and not on the freeing arm. A conditional
`HeapAllocationFreed` fact is therefore validated inside the branch evidence
but is not published as an unconditional free effect for the joined state.
An unrelated resource cannot hide the lifetime difference.

Every proposition claim closer records the kernel completion of its
clause-specific obligation. The checked path's specification carries its own
entry premises, and contract registration consumes the retained clause and
producer-path identities. It does not lower the ensure again, including
quantified ensures whose binders belong to the original obligation.

Post-return `have` completions used by a later named resource fold remain
on that returned path's checked trace. The kernel binds them to its published
program state, checks their root assumptions against the retained path,
and imports only the completed conclusions. It imports the path's execution
facts and resource observations once, then checks persistent fact deltas for
successive proofs. Resource folds recompute their semantic facts; they never
replace the path context with a proof's ambient assumptions. Direct resource closure and the fallback search both retain checked claim
receipts. The ordinary resource-closing operation proves their joint
availability before the outcome completes, independently of how its
certificate is printed.

Function body proofs open their contract entry before running tactics.
`OpenedContractEntry` selects the admitted source premises, preserves their
source occurrence indices, adds the execution environment's byte order, and
constructs the function-entry state and resource transfer. The body retains
that entry and the same indexed fact context. Opening also constructs every
undecided resource-guard alternative, with its assumptions and expanded entry
state, before executing the body. The case producer consumes an entry bound
to its caller, function and arguments, so separately supplied facts cannot be
paired with another subject. Checked executions retain the resulting opaque
case set. Conditional resource closing and registration consume those same
alternatives; neither enumerates additional entry cases for an opened proof.
Entry construction failures are reported before body tactics run.
Surface retains the selected canonical caller context for registration rather
than the earlier candidate context. Independent execution artifacts still use
the conditional checked-entry API.

Contract closing constructs the obligations needed to establish the current
contract at its checked outcome. It does not search for their proofs. Tactics
may also create obligations; omitted proofs are attempted by the implicit
solver (currently called the implicit closer in diagnostics and some driver
names). Proof completion requires every applicable obligation to be closed.

For reusable proposition postconditions, each goal is kernel-created and
retains its contract clause and evaluation requirements. A failed goal construction is
reported at contract closing; the driver never substitutes a separately
lowered surface goal. Completed claims retain their producer path identity.
Registration consumes these claim/path associations across every entry case
without reconstructing the postcondition or proving it again.

Outcome proofs also own distinct joint returned-resource, allocation-lifetime
and write-footprint obligations. The outcome's goal selector orders its source
clauses first and then these three closing goals. Completing an outcome branch
requires both sets of goals to have been opened and every applicable goal to
be closed; finishing the last written clause alone does not complete it.
The driver returns each completed outcome to the proof that owns its branch,
using its branch index and generative outcome identity. This retires only that
case; it does not import case-local facts, names or presentation into sibling
cases. Duplicate or foreign completions are refused. A case excluded by a
checked contradiction is retired explicitly, and an execution with no returning
outcomes retires its frontier without creating an outcome obligation. The
owning proof must have no open outcome branches before completion proceeds.
The outcome producer returns a path-to-branch index, so later completion does
not scan siblings to locate a case. Registration selects the retained entry
of a coherent proof, including frontier-loop proofs, and consumes its prepared
case contexts. `WholeContractProof` opens a boundary obligation and each
declared clause for every entry case before body tactics run. Clause-specific
proofs can finish while this owner still has open obligations. Ordinary
outcome completion directly retires this strategy's whole-contract obligations;
admission transfers those explicit closed cells to the shared owner. A
finished clause or case cannot stand in for another. Different cases may use different complete
execution strategies. Persistent candidate owners retain independent progress.
`complete()` returns `ContractBodyProof` only when the indexed open-goal set is
empty. Registration consumes its already constructed rule and performs no
additional clause-coverage or function-packaging check.

The opened entry is shared across a function's separate clause proofs. Checked
execution uses the entry's retained root premises; caller-proposed assumptions
cannot strengthen them. Derived facts and case assumptions travel through the
checked execution trace. Only that producer can issue `ContractEntryAuthority`,
which binds the resulting execution to the entry's generative identity.
Whole-contract admission consumes matching authorities without reauthorizing
premises, comparing execution environments or rebasing resource representations.
The declaration is retained by the owner rather than supplied again at
admission. The primary bound execution retains proof-only body annotations,
including the normalized natural loops that termination rules name. Other
clause proofs remain independent execution alternatives. Loop semantics and
call dependencies come from the selected executions.

Entry opening also retains the contract's evaluated required resources,
checked clause metadata and derived resource facts in `RetainedClosingEntry`.
Each prepared guard case owns its corresponding entry view while sharing the
checked clause metadata. The checked entry transfer prepares the static-storage
footprint input before body tactics. Range projection runs only when the open
footprint goal needs it; it never reevaluates entry clauses. The closing-goal checks consume these inputs instead of binding the
arguments, reevaluating entry clauses or projecting entry resources again.
Normal and exceptional postcondition goals use the retained entry and the
current outcome. Resource/effect closing likewise reads the proof-owned result
and state directly. Resource changes prepare a new exit view while preserving
the immutable entry input. Conditional resource exits remain work of the open
returned-resource goal; conditional effect cases consume their prepared entry
views and projections without sharing case-local facts with siblings.

A function proof opens one `WholeContractRoot` with its checked entry. Its
ordinary `ProofObject` starts with a whole-contract judgment and opens the
boundary and declared-claim cells for every prepared entry case. A persistent
index addresses each cell's native branch; completion retires that branch.

Each script works in a `ContractRootAttempt`, a persistent fork of the parent.
Its execution strategies retain their own path counters in
`ContractProofProgress`: an obligation retires only when every live path of one
strategy completes it. Partial strategies cannot combine their path coverage.
The affine `CompletedContractExecution` publishes only its own completed cells
and native execution outputs into the script fork. A failed script drops the
fork; a successful script joins its explicit closed-cell delta into the parent.
Sibling scripts do not inherit each other's speculative work.

Completing the ordinary parent root produces `ContractBodyProof`. Its partial rule
metadata comes from the root's retained producer publications, checked call
and tactic dependencies, and selected annotated subject. Registration consumes
that body proof without gathering artifacts, selecting entry matches,
reconstructing coverage or running a later completeness decision. Imported
library theorem dependencies are discharged before the root completes;
program-wide termination remains an open prerequisite, rather than an
additional check on an already completed contract.

`ProgramContractProof` opens before body execution, from the selected return
requirements, nonexternal `diverges` policies, and callback safety. Body opening adds a native body child before execution and captures its program
owner. Ordinary body completion retires that exact child directly; an unfinished
root or a proof from another session cannot close it. Body roots publish their
partial-correctness rules for modular calls and retain their own
native loop-rule outputs; each loop strategy owns the measure checked by its
back-edge proof. Strategies for the same source loop may use different measures.
An unranked strategy still prevents a ranked sibling from covering the loop.
Loop opening selects the source identity through the whole-contract owner,
checks executable shape and measure eligibility, and retains the exact statement
that its proof will execute. A successful producer carries that identity and
eligible measure in its rule; a completed rule cannot be retagged. Termination
consumes this authority without repeating source matching or escape checks.
The flat source-loop shape index and address-taken set are built once at function
setup; opening a selected loop reads its direct range and explicit body.
No common measure is reconstructed from source annotations after body closure.

Program closing has separate generation, proof execution, and completion APIs.
`ProgramContractProof::generate_termination` seals body opening and constructs
`ProgramTerminationProof`. Its immutable requirements enumerate source loops,
recursive peers and measures, direct and indirect call dependencies, and callback
address-takings. Generation can reject malformed input, but executes no loop,
recursion, or callback proof. Targeted-selection measure handling occurs here,
using the already generated recursive edges rather than retrying a checker.

`ProgramTerminationProof::into_ordinary_scope` binds these requirements to the
ordinary proposition proof object. Its root is the conjunction of the selected
return promises, callback safety, and divergence policies. The private native
scope owns their identities; Source names them with `termination_returns("f")`,
`termination_callbacks()`, and `termination_divergence("f")`. These propositions
cannot be assumed in unrelated contracts or theorems.

An optional top-level `termination by { ... }` block runs the ordinary proof
driver: `have`, logical steps, and `close()` have their normal meanings.
Omitting the block invokes ordinary bounded proof search on the same root. Its
termination strategy plans the generated dependencies and emits checked
`check_termination_local("f")`, `check_termination_component("f", strict|normal)`,
and `check_termination_callbacks()` steps, followed by `close()`. Local descent
uses the same primitives as the standalone termination API; its result is
retained as a fact and reused by strict and normal dependency steps. The
intermediate facts are written `termination_local("f")`, `termination_strict("f")`,
and `termination_body("f")`, together with their negations when refused.

`click expand --claim program.termination file.click` writes this ordinary
certificate as a `termination by` block. Replay needs no termination search;
checking a partial script does not complete the root merely because some
termination facts were established. Nested proof contexts can use termination
steps but cannot publish the program's completion. Successful completion
publishes only the root's captured return promises, never branch-local optional
facts. Diagnostics retain the descent/callee reason, while traces show the
ordinary goal and checked steps. The standalone raw termination API retains its
independent convenience executor.

Only successful proof execution constructs the affine `ProvedProgramContracts`
token. Its infallible `complete()` takes no checking inputs and only moves the
closed native proof, retained bodies, and termination rules into
`CompletedProgramContracts`. It does not analyze source, interpret verdicts,
retry proofs, or discover requirements. Source formats proof-execution failures
before calling this packaging operation.

Recursion declarations are captured by the program owner before Source theorem
or body proofs execute. This inventory fixes the declared measure kind,
parameter identity, and expression-peer permissions; declared expression peers
with incompatible measure kinds are refused at opening. Opening the selected
termination graph constructs per-function recursion authority from that retained
inventory, including unmeasured-recursion obligations and compatible component
indices. Selection can remove recursive edges, and completed tactic proofs can
add them, without reopening a completed body's declaration interface. Independent
termination APIs open the same inventory from their explicit inputs before
executing termination proofs.

Call-ranked recursion also opens a descent cell for every entry case in the
ordinary contract root. The execution core captures its recursion context before
the body begins. Each native statement transition carries its own context beside
its theorem and ordinary premises; the recorder consumes the opaque native path,
so Surface cannot splice a context onto another theorem. Tactic application uses
the same opened context. Loop opening retains its call footprint, and summary
application answers for recursive peers as well as self-calls.

The trace retains this descent context while its outcome obligations remain open.
Ordinary outcome completion retires the captured descent cells; failed attempts
publish nothing. A completed root packages native descent completion, which local
termination consumes directly without a source/loop-anchor coverage walk.
Independent termination inputs without an ordinary root retain their separate
coverage analysis. Source numeric measures, including bare C parameters, and
named structural resource binders all use call producers. A numeric call owes
nonnegativity and strict descent from the immutable entry value; assigning the
C parameter does not change that entry value. A structural call passes an
instance whose model is strictly contained in the entry model.

Anonymous resource measures (`decreases list(node)`) also use call producers.
The opening captures the exact entry occurrence of the measured resource.
Unfold and observe retain bounds for the owned children they produce, even
when observation projects those children to views. Folding constructs a
parent bound from its supplied children; a leaf uses only the branch's
established lower bound on the entry witness's height. The bounds belong to
opaque resource occurrences, so an unrelated returned resource cannot inherit
descent merely because its resource term is equal. Calls consume this native
evidence through ordinary descent obligations, and completed roots require
no structural source-body walk. Explicit legacy standalone termination plans
retain their compatibility analyses.

Ordinary and independent termination inputs have separate constructors.
`ContractBodyProof` retains `CompletedBodyTermination`, whose loop namespace
and descent authority are nonoptional native outputs of the whole-contract
root. Program obligation generation selects that typed input by its body
owner; it never probes a reusable rule for missing evidence and then runs a
legacy analysis. Completed-body local steps consume retained loop ranking
and exit evidence directly. Legacy numeric/resource plans are refused when
opening an ordinary program; standalone termination APIs retain their
explicit independent adapter. Raw rule candidates already owned by a completed
body are excluded before that adapter runs. Conservative call inventories are
captured at body opening, so a missing execution trace does not cause a later
source-body walk.


Ordinary program opening declares a body cell for every selected contract,
including startup, source-only and diverging contracts. Only the captured native
body producer retires that cell. A body whose entry was never opened remains
pending; neither a recursive hypothesis nor a reused rule can substitute for it.
Selected-function runs retain their explicit assumptions for unselected functions.

Modeled pthread creation has an auxiliary termination bootstrap before body
execution. It uses typed native inputs for bodies already completed and explicit
independent inputs for other code. Its termination rules cannot retire body cells
or seal the program. This preserves nested thread creation without treating an
auxiliary termination proof as a completed ordinary contract. Synthetic one-call
theorem proofs likewise use fresh entry sessions without a program owner; their
extracted rules cannot close the enclosing program's body cells. Build-time guards
keep Source and ordinary program orchestration off the standalone termination API
and confine legacy loop preparation to the explicit input adapter.

Concrete loop-exit coverage is fixed in the ordinary body's source namespace
at opening. Loop/body source mismatch is refused before proof execution.
Successful `ApplyVerifiedRules` execution publishes coverage for loops it ran
concretely or avoided, with summary-owned loops excluded. A loop summary also
retains the nested-loop execution mode and coverage established by its producer;
an outer summary does not automatically prove its inner loops terminate.
Script joins intersect coverage, and discarded attempts publish nothing.
`VerifiedFunctionRule` retains this native evidence for modular reuse and
program termination. Local termination consumes it by loop index, without
matching completed bodies or inferring execution from annotation flags.
Independent API inputs without an ordinary owner retain their separate input
adapter, which runs before termination obligation generation and leaves already
owned evidence untouched.

Every declared claim owns a root cell for every entry case, including source-only
state clauses and other nonmodular postconditions. Reusable-rule eligibility
is separate from this obligation inventory. Opening a source-only proposition
proof captures its selected declaration key from the outcome's claim table;
ordinary proof completion retains that key and outcome identity. A generic
proposition completion, another clause's proof, or a resource receipt cannot
close it. Completed outcomes retire these captured cells through the same
persistent progress counters as reusable claims. Completing only the boundary
leaves omitted source clauses open, even if the frontend skips them.

Startup and source-only contracts retain native termination subjects without
gaining unsupported modular rules; rule eligibility is fixed at body opening.
Source-only clauses keep their existing ordinary outcome scopes. Explicit
whole-contract `sorry` admissions remain dev-only assumptions and produce no
checked contract. Synthetic one-call `executes` proofs continue to use partial
body rules for contract-refinement inference.

Function-proof sessions share persistent source-definition indexes but own
fresh entry/root slots. Clause scripts share the same session; another function
or one-call theorem proof starts a new one.

The checked execution producer constructs `PublishedFunctionOutcome` alongside
each path, retaining its specification, theorem, and raw result/state together.
Opening an ordinary outcome allocates a fresh proof identity and retains that
producer publication. Completing a clause publishes the evidence held by that
exact goal through its retained publication; it does not accept a separately
supplied receipt or reconstruct and compare specifications, results, memory,
or locals. Reopening the same execution keeps proof owners distinct.

The checked body producer retains the completing statement and exit inputs in
`CheckedReturnSeed`. Opening an ordinary outcome forks a `ReturnRewriteProducer`;
completed propositions and resource exchanges advance that producer using only
the new facts and selected exchange. Preparing contract closing uses its retained
completion, without replaying C execution history.

`ContractExecutionOwner` owns one execution strategy and its opened outcome
identities. Ordinary completion directly installs the outcome's current producer
publication, path and completed exit, and retires its whole-contract cells.
Refutation discharges the selected outcome without fabricating exit evidence.
The completed ordinary proof hands back this execution directly. Native outcome
completion also projects its held resource evidence into the checked-execution
fields required by independent execution-only consumers. Checked resource keys,
returned owners, and boundary status are produced there, without rechecking the
receipts. Source has no parallel per-path receipt arrays or metadata setters to
reinstall after completion.
Independent conditional execution artifacts have no opened-entry authority and
retain their separate entry preparation and rule-packaging APIs.

Closing goal state is fixed-size and shared proof forks retain independent
updates. An explicit `close()` discharges the selected closing goal using
its retained outcome, receipts and body effects. Written `close()` selects the
same operation; the implicit solver schedules it for each omitted closing proof.
Expansion records one `close()` per completed goal, so rechecking requires
no implicit proof of these obligations. A checked resource transition retains
resource/lifetime evidence without silently closing either goal. Explicit
resource changes reopen the affected goals. Packaging an exit completion reads
only the closed-goal state and packages the checked path; it performs no
additional resource or effect check. With implicit solving disabled, an omitted closing step leaves its goal
open. Diagnostics name that goal and distinguish a written tactic refusal from
an implicit solver failure; a proposition-only closer names the actual closing
goal instead of claiming there is no goal.

A clause-specific proof closes the joint resource prefix through
its last selected resource clause; it cannot certify later clauses whose
separate proofs have not run. Only a completion of the entire resource prefix
supplies whole-boundary/body-safety evidence, which registration requires for
every entry case. Boundary resolution uses the proof-owned outcome after its
explicit resource operations. Boundary refusals retain the original execution error. Contract
registration consumes exit completions across entry cases without preparing
resource/effect paths again. The independent execution-only API still checks
its supplied execution because it has no completed proof obligations.

A function with proof-local clauses, such as a postcondition referring to
`at(region(0).entry, ...)`, has no reusable modular proposition contract.
Its source clauses remain ordinary local proof obligations. This distinction
is established before opening goals; a failed registered contract goal never
falls back to a local lowering.

There is one lowering. A claim goal is the contract's elaborated ensure
lowered by the kernel at the path's outcome (`FunctionEnsureGoalContext::goals`); a
registered predicate ensure is the predicate identity, which the proof
unfolds on the goal, and an explicit closer also tries the unfolded body
when the proof unfolded that predicate. Every proposition a proof states,
a `have`, a `rewrite` equality, a `frame using` premise, a resource witness,
goes the same way: elaborated into the kernel's spec form exactly as a
contract clause is (`elaborate_fixed_state_proposition`, with the proof's
recorded states, `old(...)` as the function entry, `result`, and the
proof's current locals as fixed values) and lowered by the kernel
(`program_lower_spec_proposition_at_state`), under one reasoning policy
(`proof_lowering_assumptions`): a proposition that applies a pure function
keeps its memory reads symbolic. A `branch ensuring` or proof `if ensuring`
fact is checked in each arm under that same policy and the arm's facts, and
its elaboration reads a local array by its element type and binds
quantifiers as a `have` does, so an arm holds an interface fact exactly when
a `have` of the same text there would; an expression a proof evaluates goes
the same way (`elaborate_fixed_state_expression`,
`program_evaluate_speprogram_expression_at_state`). Every pure-function call stays a
typed logical application during lowering, including calls whose arguments
are constants. Only the checked `unfold(function(args))` proof step exposes
one instantiated defining equation; lowering itself never executes Click.
Likewise, a match on an unknown algebraic value remains one symbolic term
rather than creating execution paths. A function's requirements at the proof's
entry, an applied theorem's requires and conclusion, and a pure theorem's
goal are elaborated and lowered the same way, so a declared standard
theorem matches its kernel axiom by form. So are the C fragments stated
outside proofs: a resource clause's quantity, arguments, and segment bounds,
an effect footprint, a resource definition's reads
(`evaluate_program_expression_through_kernel`), and a predicate body unfolded on a
kernel proposition, which is elaborated with the parameters bound to the
decoded arguments and lowered at the decoded state. A C fragment stated at
a state that does not justify a load it makes is refused there, unless the
clause allows symbolic contract loads (a resource segment, an effect
footprint inside a folded composite), in which case the load stays the
symbolic term kernel execution represents it as and exposes its viewability as
an obligation. The surface has no evaluator of its own. A count named at a recorded state
is that state's population. A negated condition is the condition with the
other value, as an execution represents the branch it did not take, and
viewability terms are canonical, so a proposition lowered anywhere is
represented as the execution's facts are. The kernel lowering leaves a load's
viewability as an obligation. Claim opening uses the ordinary obligation
channel to discharge it from the path's facts or an explicit proof. A
completed postcondition is consumed by its clause and producer path, including
an authorized rebase of that same path; there is no second lowering to match.
A claim with no `by` block ends, like every script, with the implicit closer
(`SmartSite::Implicit`, which diagnostics call the implicit closer): the direct
logical closure of the kernel's claim goal from the outcome Proof or, when
that does not apply, the search behind `close()`, whose certificates are
checked like explicit ones; each
records the completion like any other closer. A
resource ensure is an exact check against the outcome that returns an opaque
witness bound to the claim key and checked execution path. Effect propositions
retain their checked proposition completion. A vacuous claim retains the
kernel-created divergent or opposite-family outcome that discharges it.
Grouped presentation records these witnesses by claim key; serialized tactics
cannot substitute for missing completion evidence.
A proof-produced execution path also retains the body outcome checked against
its trace before the contract exit rule. Completion binding checks that exact
origin or the certified exit outcome, including the normal/exceptional family.
This preserves aggregate-return completions when exit restores caller block
layout metadata; it does not ignore memory differences or run the proof again.
When nothing closes a claim, the diagnostic names the reason: the goal's
lowering, a rewrite that did not apply, or the unclosed goal with the sides
its comparison evaluated to. Certification proves nothing a second time: a
lowered ensure that folded to a constant truth is decided by that
evaluation, and every other form needs a matching completion. Proofs of one
function structure their paths differently (a `branch` proof continues once
from the joined state and publishes the joined path, whose result names the
join's fresh variable; an automatic proof publishes each arm) and may run at
different representations of the entry (one observed a resource first), so
certification keeps every artifact reusable at the contract entry as its
own path set and accepts a claim when, in every resource-guard case, one
path set certifies it on all of its paths; each set is a complete execution
of the function, so any one is authority, and a set is prepared for claim
checking only when a claim is judged over it. A rewritten claim goal stays
on the retained outcome proof, so the closer after the rewrite records the
claim goal the proof was rooted at rather than the rewritten form.

That lowering is not an isomorphism, so it reports what it did. A quantified
body's path facts are folded into kernel implications that no written
connective produced, and a quantifier binds its written name to a kernel
variable the written syntax never names. `program_lower_spec_proposition_at_state`
therefore also returns the head chain of the proposition it built: per
outermost node, whether lowering inserted it as a path-fact or obligation
guard, or the spec wrote it, and, for a written universal, the written name
with the kernel variable it was bound to. The chain and the proposition come
from one traversal inside `wrap_path_context`, so the record cannot drift
from what it describes. A newly stated goal keeps that chain in its
presentation. `intro` reads it rather than inferring a correspondence from a
shape the written syntax happens to share: a hidden guard is introduced with
the written goal still focused, a written implication consumes the written
connective and retains the checked Surface-to-kernel antecedent pair with the
structural conjuncts it refines to, and a written universal binds the written
name to the variable the introduction actually freshened to. Later citations
of an introduced antecedent read the retained pair, because re-lowering a
written antecedent runs under the fact context the introduction changed and
produces no path at all for an antecedent no state satisfies. A goal whose
kernel proposition did not come from a lowering performed for it carries no
chain and refines its written form structurally.

A body's path facts may mention the variable its quantifier binds, so they
are placed under that binder, never beside it: hoisting one leaves the same
variable free in the guard and bound in the body, which is a proposition no
written proof can state or introduce. The polarity follows the quantifier. A
guard restricts a universal's domain, so it is the antecedent of the
implication `wrap_path_context` inserts, and the chain records it after the
`WrittenUniversal` entry for that binder. A guard restricts an existential's
witness, so it is a conjunct of the quantified body instead; guarding by
implication there would make the claim vacuously true of every witness the
guard excludes. Nothing under an existential binder is reachable before a
`witness` names its value, so the head chain stops at the binder and the
proof reaches a guard conjunct with `all`.

`RecordedStates` is a persistent map from `ProgramPointSelector` to `ExecutionState`.
A selector is either a static C `ProgramPointRef` or a proof-local mark. A
recorded `ExecutionState` is logically complete, but its memory, facts, and resources
are immutable shared roots: recording or branching a state copies only
small roots and changed map paths rather than materializing the whole state.

Premise reconstruction seeks statement entries in that persistent tree:
entries at or before the selected anchor, nearest first, followed by later
entries in forward order. It does not enumerate and sort the complete map
before trying a nearby candidate. Tree traversal and synthesis check the
active work budget and deadline; an exhausted search stops before trying
further states or presentation fallbacks. Every accepted Surface form still
has to lower to the exact selected kernel premise. Cross-state equality
reconstruction uses the visited entries and checks cancellation per operand.

Lowering and fixed-state proofs read execution data through `ExecutionView`, a
borrowed view of the frontier, recorded states, surface
forms, execution facts, and the `old(...)` reference state. It is built from
the presentation and its kernel core (`ExecutionProofState::view`, or
`ExecutionView::new` for a
planner's scratch state); nothing in it borrows a cursor.

A surviving source or expansion cursor may own syntax position, focus,
attribution, and diagnostics. It must not own facts, resources, `ExecutionState`, an
execution frontier, or authority to construct a successor.

## Smart planning

Planning modules inspect `Proof`, rank candidate operations, and explore
persistent descendants within deterministic budgets. They use the same checked
simple and structural operations as explicit tactics. A candidate is not
accepted merely because the planner labels it successful; success is a
completed checked descendant.

A checked derivation for proof search is added only for a common, bounded,
checkable shape: it must emit proof steps the kernel checks one at a
time and a certificate can encode. A search result guides diagnosis. The emitted steps establish the goal.

For expansion, the completed proof's lineage is filtered to the selected
source site and rendered as an explicit Surface Click proof. The complete
rewritten source is then parsed and verified through the ordinary entry point.
That check validates lineage extraction, surface synthesis, rendering,
parsing, lowering, and source interpretation without preserving a second
semantic proof engine.

## Kernel derivations

Kernel structures in `src/kernel/primitives/derivations.rs` represent typed
semantic evidence and obligations. They are separate from the persistent proof
object and from surface expansion: surface proof steps encode user-reviewable
operations, while kernel derivations justify the underlying proposition,
execution, memory, or resource transition. `Theorem` is authority for an
established proposition; `PropositionDerivation` retains the checked reasoning
tree; other typed evidence records execution and memory transitions.

A `PropositionDerivation` is *found* by planning and *validated* by the
kernel. The logical search that finds one — the recursion over a goal's
connectives, the disjunction arm choice, the antecedent assumption, the
finite instantiation, the case split over disjunction facts, the singleton
substitution — lives in `kernel::search::ProofSearch<PureFactContext>` in
`src/kernel/search/proposition_search.rs`. It advances state only through
checked kernel operations (`assume_proposition`, `restricted_to_facts`)
and public exact queries. The checker, `PropositionDerivation::check`, stays in the kernel:
it is local, deterministic, and bounded by the derivation it was handed.

Explicit kernel proof operations do not call that proposition planner. A kernel operation that
needs to know whether a proposition holds uses an exact route — the fact
index, the frozen condition checker on a bare condition, or the retained
atomic memory and resource checkers — or emits the proposition as an
obligation for an ordinary tactic to prove. Because a derivation carries no
authority until it is checked, a planning bug can lose a proof but cannot
issue one.

### Kernel authority boundary

Three standing rules keep the boundary where the 2026-09 cleanup left it.

- **The atomic theory checkers are frozen.** `PureFactContext::decide` and
  the atomic memory and resource checkers (`proves_memory_loadable`,
  `proves_memory_access`, `proves_resource_separate`,
  `proves_resource_contains`, and the memory-DAG and canonicalization
  equality walks) decide one named condition or atomic proposition by a
  fixed rule set over indexed facts. Add no rule to them. Their remaining
  whole-context loops are indexing debts under the efficiency contract, not
  license to reason more. A kernel site may call `decide` only on a bare
  `ConditionIs`.
- **Selections must raise; discharges become obligations.** A kernel
  operation that asks whether a proposition holds uses an exact route or
  emits the proposition as an obligation. One that must choose among
  candidates the kernel itself enumerates lowers the choice as a finite
  disjunction so the proof proves one disjunct, closes it with
  `close()`, and expansion prints it; open
  choices use the existing `instantiate`, `witness`, `obtain`, `rewrite`,
  and `transport` syntax.
- **Retained evidence names premises, never a context.** A derivation leaf
  carries the propositions it cites, and its check rebuilds a context from
  exactly those.
- **A cited Surface form must still lower to the fact it cites.** The surface
  map records which Surface form produced which kernel proposition, but a
  form can stop denoting that fact where the certificate is written: a proof
  `match` arm's case fact states the scrutinee's constructor at unchanged
  function entry, and once the arm has refolded its instance, `c.model ==
  C(..)` reads the refolded field instead. A refold is the only move that
  does this, so resolving a premise written as a constructor equation lowers
  the candidate again at the state it will be rechecked in: the recorded pair
  settles that shape only when the form has no lowering there at all, and a
  form that lowers to some other fact is not a Surface form for this one. The
  stale case falls back on the entry-anchored `old(c.model) == C(..)`, which
  does lower to it, and only where the bare pair would have answered — a
  lookup that reached no Surface form still reaches none. Every other premise
  keeps the cheap recorded-pair route, because re-lowering every candidate
  costs a smart `have` about half its real-time budget again.
  A fixed-state certificate inside a proof `match` also retains that site's
  lexical bindings. If a selected comparison has no recorded Surface form, it
  may reconstruct a match-bound scalar name, but only when lowering that name
  in the same scope yields the exact available kernel premise. The emitted proof
  keeps the source name, never the kernel's fresh variable name.
  For an implication guarded by algebraic equality, `close()` first tries to
  refute the guard with an indexed model equality and direct normalization.
  A successful candidate emits the ordinary scoped `have`, `rewrite`,
  `intro`, and `contradiction` operations, before selecting or raising facts
  connected to the entire implication. A missed candidate leaves the ordinary
  closure search available.

The target invariants are:

- explicit and smart tactics advance one `Proof` through checked operations;
- smart success is a completed checked descendant, not an unchecked plan;
- selectors resolve against the focused state where their operation applies;
- proof checking doesn't depend on failed-search history;
- expansion extracts exact attributed lineage and emits verifiable Surface
  Click;
- persistent proof-state sharing must not permit mutation of an earlier state;
- instrumentation can observe work but cannot change the validity decision.
