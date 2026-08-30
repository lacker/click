# Proof objects

Click's internal `Proof` object is the persistent checked representation of an
evolving proof. It lets explicit tactics and smart search share one semantic
transition boundary while retaining enough provenance to explain or expand the
result.

## Persistent proof state

The kernel `ProofObject` owns an immutable `ProofState` and the focused branch
cursor into that state. The language-layer `Proof` wrapper pairs that opaque
handle with a shared checking context and Surface provenance `ProofNode`.
Applying a checked operation returns a successor that shares unchanged
structure with its ancestor. A smart tactic can therefore branch, inspect
alternatives, and abandon candidates without cloning the complete logical or
execution state.

The kernel owns branch and split identities and the persistent open-branch
topology in `src/kernel/proof/branches.rs`; the remaining checked transitions
are being moved across the same boundary incrementally. Its
surface-independent persistent containers already live in
`src/kernel/proof/storage.rs`, while typed execution-frontier state lives in
`src/kernel/proof/execution.rs`. That module now owns the complete
surface-independent `ExecutionProofCore`, not only its frontier. The persistent
fact store's structural keys live in `src/kernel/proof/fact_keys.rs`. The fact store's semantic matching,
transport, conflict, and snapshot-equivalence rules live beside those keys in
`src/kernel/proof/fact_reasoning.rs`; Surface Click fact selection, diagnostic
rendering, and budgeted smart premise search remain in the language layer.
The persistent `ProofFacts` store and all of its semantic indexes live in
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
Conjunction extraction and explicit universal instantiation likewise accept
lowered inputs, then let the kernel validate availability, guards, and the
resulting fact before it publishes a successor.
For proposition `if` and `cases`, the kernel allocates the audited split and
sibling identities, checks complementary or available case facts, and owns the
closed-arm join. Surface provenance independently proves that serialized arm
steps descend through the exact split marker; it never manufactures branch
state. Logical `cases` at an execution frontier uses the same operation while
sharing the unchanged execution core between both fact-local siblings.
Result-aware outcome state uses the same split as execution state: the kernel
owns its result, C state, facts, requirements, and crossed effects, while
Surface proposition records and diagnostic provenance remain an opaque
language presentation.
Untrusted smart selection
lives outside `proof_object/` and may inspect its read-only planning interface
or publish descendants created by checked proof operations.
Contextual Surface Click lowering likewise lives beside the language-layer
proof drivers; the checked core retains only the derivation lineage from which
surface certificate provenance is extracted.

The borrowed parser, project-environment, lowering, and diagnostic inputs are
grouped in `src/lang/click/proof/language_context.rs`. They are language
context, not persistent proof state. Surface `ProofStep` lineage and checkpoint
extraction are isolated in `proof_object/provenance.rs`; that lineage records
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

`Proof` provenance retains the surface-expressible operation that produced each
checked successor. `ProofCertificate` is the current structured serialization
of those operations as `ProofStep` values, including nested scopes and
branches. It can be rendered back to surface tactics for expansion. The
serialization carries no semantic authority of its own and need not exist
during ordinary verification in the intended architecture.

## Execution state inside a proof

Kernel `ExecutionProofCore` owns the semantic execution state for one proof
path: the `CState`, typed frontier (program point, region, region start state,
and continuations), checked execution facts and loop rules, function-entry
prerequisites and derivations, freshness counters, loop-effect goal, region
flags, structured-branch flags, and unfolded kernel predicates.

Kernel `ProofExecutionState` pairs that core with an opaque language
`ExecutionProofPresentation` containing only Surface Click construction data:
recorded snapshots and their selectors, source spellings,
case assumptions, frontier loop clauses, planned statement transitions,
branch and outcome provenance, deferred post-execution tactics, and the
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
as one `Construction` gate; a bounded execution gives each explored path its
own sink and synthesizes them at the join. It lives only as the execution
snapshot of a `Proof` goal: the checked drivers advance a `Proof`, and every
source or generated proof tree is checked that way. The earlier interpreter
that advanced this context as a parallel engine is gone; the snapshot owns the
C store and the goal owns the facts.

`RecordedSnapshots` is a persistent map from `SnapshotSelector` to `CState`.
A selector is either a static C `ProgramPointRef` or a proof-local mark. A
recorded `CState` is logically complete, but its memory, facts, and resources
are immutable shared roots: recording or branching a snapshot copies only
small roots and changed map paths rather than materializing the whole state.

Lowering and fixed-state proofs read execution data through `ExecutionView`, a
borrowed view of the frontier, recorded snapshots, surface
spellings, execution facts, and the `old(...)` reference state. It is built from
the presentation and its kernel core (`ExecutionProofState::view`, or
`ExecutionView::new` for a
planner's scratch state); nothing in it borrows a cursor.

A surviving source or expansion cursor may own syntax position, focus,
attribution, and diagnostics. It must not own facts, resources, `CState`, an
execution frontier, or authority to construct a successor.

## Smart planning

Planning modules inspect `Proof`, rank candidate operations, and explore
persistent descendants within deterministic budgets. They use the same checked
simple and structural operations as explicit tactics. A candidate is not
accepted merely because the planner labels it successful; success is a
completed checked descendant.

A checked `simp` derivation is added only for a common, bounded,
checkable shape: it must emit proof steps the kernel checks one at a
time and a certificate can encode. That the search-based `simp` decision
procedure could decide a goal is not a criterion; it is a diagnostic, not
an authority.

For expansion, the completed proof's provenance is filtered to the selected
source site and rendered as an explicit Surface Click proof. The complete
rewritten source is then parsed and verified through the ordinary entry point.
That check validates provenance extraction, surface synthesis, rendering,
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

The target invariants are:

- explicit and smart tactics advance one `Proof` through checked operations;
- smart success is a completed checked descendant, not an unchecked plan;
- selectors resolve against the focused state where their operation applies;
- proof checking doesn't depend on failed-search history;
- expansion extracts exact attributed provenance and emits verifiable Surface
  Click;
- persistent proof-state sharing must not permit mutation of an earlier state;
- instrumentation can observe work but cannot change the validity decision.

The former chronological proof-object design log is preserved at
`design/proof-object-api.md`; this page describes the current architecture.
