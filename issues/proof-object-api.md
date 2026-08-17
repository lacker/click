# Proof object API

## Summary

Click needs one immutable checked proof object as the boundary between the
megakernel and smart tactics. A smart tactic may inspect, cheaply clone, and
search over `Proof` values, but it must not advance a proof through private
semantic operations. The only way to obtain a successor is to apply an
explicit [`SimpleProofStep`] through the ordinary checker, or to use an
equally explicit audited structural operation for branching and scopes.

Every successful successor therefore retains the exact structured simple
proof that produced it. Expansion reads that structure; it does not
reconstruct a certificate from semantic aftermath or rerun search. Arbitrary
smart tactics can be incomplete, expensive up to their enforced budget, or
produce inelegant proofs without entering the soundness boundary.

This is the next architectural priority. Do not repair individual smart-tactic
certificate failures by adding another planner record, evidence wrapper,
lowering pass, or independent replay. Migrate them onto this API.

## Violated invariant

The intended invariant is:

> A smart tactic can inspect and fork proof objects, but it cannot advance one
> except by applying and retaining a `SimpleProofStep`. Every resulting proof
> object can expose the complete structured simple-step derivation from its
> root to its current open goals.

The current implementation does not enforce that invariant. Semantic proof
state, smart planning, surface-certificate construction, replay bookkeeping,
and expansion capture are mixed in `ProofReplayContext` and
`TacticReplayState`. Smart execution can use planning-only policies and
private transition evidence, mutate a temporary semantic context, lower the
result afterward into a `ProofCertificate`, and independently replay that
generated proof to discover whether the spelling described the transition
accurately.

That architecture double-implements proof operations:

1. a smart path discovers and performs an internal operation;
2. certificate construction tries to infer the corresponding simple steps;
3. independent replay performs the operation again through the simple path.

It is a recurring source of missing premises, snapshot-spelling failures,
branch disagreement, misleading deadline attribution, and duplicated kernel
work. `atomic-derivation-returns-premises-not-steps.md` is one measured
instance: the prover returns a conclusion and premises but discards the rule
steps it used, so certificate construction searches again. The quarantined
owned-vector smart `step()` is another: planning constructs and executes a
transition, then expansion validation times out while executing the generated
`step() using` a second time even though that explicit simple step is fast
when used directly.

## Canonical vocabulary

Use these terms consistently in Rust, diagnostics, documentation, and issue
discussion:

- **`Proof`**: the immutable checked proof object used by smart tactics. It
  contains the current semantic situation and persistent provenance from
  accepted steps. A `Proof` may still have open goals.
- **`Goal`**: one unresolved judgment inside a `Proof`. Pure propositions, C
  execution frontiers, resource obligations, and loop effects may be distinct
  goal variants.
- **`SimpleProofStep`**: one explicit deterministic certificate operation
  checked by the megakernel. A step may be powerful and C-specific; "simple"
  means that it names its rule and evidence, not that its implementation is
  small.
- **`ProofCertificate`**: the structured simple-step derivation exposed by a
  `Proof` and rendered by expansion. It contains sequence, branch, and scope
  structure whose leaves are `SimpleProofStep` values.
- **`ProofNode`**: a private persistent-DAG storage node. It is an
  implementation detail, never the name of the smart-tactic API object.
- **`SmartTactic`**: an untrusted, budgeted search procedure over `Proof`
  values. Its search strategy is outside the soundness boundary.

Reserve **replay** for independently checking a serialized or separately
supplied certificate: explicit source verification, `click expand`'s final
rewrite check, `click audit`, and focused tests. Applying a candidate step
during smart search is that candidate's ordinary check, not replay. Ordinary
smart-tactic success must not rerun its successful path merely to validate a
second representation.

The first migration checkpoint moves existing names out of the way rather
than giving them overlapping definitions:

- the parsed-source enum is `SourceProof`;
- the exportable certificate structure is `ProofCertificate`;
- keep `SimpleProofStep` for deterministic certificate instructions;
- retire `ProofReplayContext` as a smart-tactic interface rather than
  relabeling its mixed mutable contents as `Proof`;
- keep certificate builders and DAG nodes private; smart tactics never mutate
  either directly.

`Theorem` remains the abstract proposition evidence produced by trusted
kernel operations. It is not a synonym for `Proof` or `ProofCertificate`.

## Intended API shape

The exact Rust layout may evolve, but the capability boundary should look
like this:

```rust
pub struct Proof {
    // Private persistent representation.
    node: ProofNodeId,
}

impl Proof {
    pub fn goals(&self) -> impl Iterator<Item = GoalRef>;

    pub fn inspect(&self, goal: GoalRef) -> GoalView<'_>;

    pub fn apply_step(
        &self,
        goal: GoalRef,
        step: SimpleProofStep,
    ) -> Result<Proof, StepError>;

    pub fn is_complete(&self) -> bool;

    pub fn certificate(&self) -> ProofCertificate;
}
```

All fields and constructors that could mint an advanced proof remain private
to the audited proof-object implementation. Query APIs expose read-only facts,
resources, goal shape, frontiers, and indexed candidates. They may help a
smart tactic choose a step, but they do not return authority to mutate state
or close a goal.

In particular, a query that discovers that a proposition is provable must
return candidate `SimpleProofStep` values (or a `ProofCertificate` composed of
them), not a bare Boolean, anonymous theorem, premise set, or internal
transition that lets search bypass `apply_step`.

`apply_step` atomically:

1. checks the supplied step against the selected goal and current context;
2. creates the successor semantic state and any successor goals; and
3. appends that exact step and its structural outcome to the persistent
   derivation.

There is no successful state transition without matching certificate
provenance and no accepted certificate step that was not checked.

## Completion and goals

A partial `Proof` certifies a derivation from its root to its current open
goals; it does not yet prove the root. A complete `Proof` has no open goals.
Only an audited terminal operation may export the resulting verified claim or
theorem.

The current implementation represents these concepts inconsistently: C proof
progress lives in an execution frontier, pure `have` proofs keep a separate
goal and `goal_closed` flag, loop effects use an optional specialized goal,
and final claim certification happens elsewhere. The new `Proof` should own a
typed goal collection so completion is an explicit invariant rather than a
convention spread across callers.

Do not require every smart tactic to finish the entire root proof. A local
tactic succeeds according to its operation: it may discharge one focused
goal, advance one C frontier, or refine one goal into subgoals while preserving
the enclosing proof's other goals.

## Branches, scopes, and DAG structure

Branching must be proof-object infrastructure rather than logic recreated by
each smart tactic. Applying a step may replace one focused goal with zero, one,
or multiple labeled successor goals. Smart search can select and solve those
goals independently. Cheap proof clones share their common semantic and
certificate prefixes.

The persistent representation may be a DAG with explicit sequence, split,
scope, and join nodes. `ProofCertificate` exposes a deterministic structured
view suitable for Surface Click. Creating that view may traverse and render
the retained structure; it must not rediscover rules, choose premises, rerun
theories, or infer branch ownership from final states.

Any operation that joins branches, opens or closes a resource scope, creates
logical subgoals, or finalizes a loop is part of the audited proof-object core.
It must record its certificate structure when it happens. A private branch
merge that later asks certificate construction to reverse-engineer the merge
is the same forbidden split representation as the current planning path.

## Smart-tactic facilities

The shared search layer should provide bounded, reusable operations over
`Proof` rather than forcing each tactic to manage mutable replay contexts:

- read-only indexed inspection of the focused goal, facts, resources,
  snapshots, and execution frontier;
- cheap cloning/forking and dropping failed descendants for backtracking;
- `apply_step` and audited structural operations;
- deterministic goal selection and branch traversal;
- bounded DFS/BFS, `first_success`, `try_steps`, and "solve every open goal"
  combinators where they prove useful;
- memoization keyed by semantic proof-state identity, not complete derivation
  history; and
- the existing deterministic search budgets and real-time backstops.

Smart tactics remain responsible for useful heuristics and diagnostics.
`apply_step` makes them irrelevant to soundness, not irrelevant to
performance, termination, expansion quality, or user experience.

Current smart tactics fit this model:

- bare `apply` searches for premises, then applies `ApplyTheoremUsing`;
- bare `transport` searches for premises, then applies `TransportUsing`;
- `simp` searches among explicit normalization, extraction, rewrite, logical,
  and theorem-application steps;
- `step()` searches for prerequisites and explicit transports, then applies
  `StepUsing`;
- `execute()` and `execute_until()` repeatedly search for and apply statement
  steps across open execution goals;
- `frame()` searches for a region and premises, then applies `FrameUsing`;
- `auto` orchestrates the same proof-object operations.

If a smart tactic needs a semantic operation that no `SimpleProofStep` can
express, that is a missing certificate-language operation. Add a deterministic
explicit step backed by the megakernel; do not add a private tactic escape
hatch.

## Megakernel boundary

This design preserves the megakernel philosophy. Click may have many powerful
`SimpleProofStep` variants for C execution, checked arithmetic, memory,
resources, contracts, function calls, loops, and domain-specific theorem
schemas. One step may perform substantial specialized work.

The boundary is not "small kernel versus powerful tactics." It is:

- the megakernel owns trusted, deterministic state transitions and theorem
  production; and
- smart tactics own arbitrary heuristic selection and search over those
  transitions.

The proof-object core, not every tactic, is audited for soundness. That core
includes initial-proof construction, `apply_step`, structural split/scope/join
operations, completion/finalization, and certificate serialization. Parser and
lowering correctness remain part of accepting Surface Click, and kernel axiom
implementations remain trusted as documented in `docs/kernel.md`.

## Efficiency requirements

The API must satisfy `docs/advanced/verification-efficiency.md` by
construction:

- cloning a `Proof` for search is constant or logarithmic in total proof and
  project size;
- applying one step costs `O((q + d) polylog N)` amortized, where `q` is its
  explicit input and `d` its semantic/certificate delta;
- facts, resources, goals, environments, C states, snapshots, and certificate
  prefixes use persistent structural sharing rather than complete clones;
- appending a linear proof node is constant or logarithmic apart from the
  step's own payload;
- dropping a failed search branch does not traverse or copy its shared
  ancestors;
- memoization compares stable shallow semantic identities, not complete proof
  histories or deep state structures; and
- extracting a certificate is output-sensitive in the emitted certificate,
  not in unrelated search branches that were discarded.

Do not first build the API with whole-state clones and defer representation
work. Cheap forking and local step application are requirements for the
architecture to support real smart search.

## Migration plan

Implement this in independently green vertical slices; do not replace the
entire verifier in one change.

The first implementation checkpoint provides a persistent pure-goal `Proof`
with checked `ApplyTheoremUsing`, `Assumption`, and `Normalize` steps. Pure
scripts of the exact form `apply(...); assumption();` now select the applied
theorem's instantiated premises and advance only through `Proof::apply_step`;
they export the retained certificate without the ordinary construction/replay
gateway.

The second checkpoint extends the same private `Proof` core to point-level
goals and migrates `have proposition by { apply(theorem); }`. Premise search is
now a selection-only query; the chosen `ApplyTheoremUsing` is checked once by
`Proof::apply_step`, which closes the point goal when the theorem's checked
conclusion is exact. The retained nested certificate is appended directly to
the enclosing proof, while `click expand` still prints and independently
verifies it. A regression verifies that ordinary construction emits no
`surface certificate replay` event for the migrated claim and that deleting a
selected premise from the expanded proof is rejected.

The remaining pure forms, point-level smart forms, and all C-execution tactics
still use the legacy path and remain migration work.

The third checkpoint introduces an explicit open `ExecutionFrontier` goal and
an output-sensitive per-step fact delta. Top-level bare `apply` now selects
candidate premises without applying the theorem, submits the resulting
`ApplyTheoremUsing` to `Proof::apply_step`, incorporates only the successor's
new facts, and appends the retained step directly. Ordinary verification no
longer runs `complete_smart_tactic` for that operation; a regression counts
one simple apply check in the later whole-certificate replay rather than a
construction replay plus that final check. Proposition-only closers are
transactionally rejected on an execution-frontier proof.

The fourth checkpoint extracts mid-execution `TransportUsing` into one
audited `check_point_fact_transport_using` operation shared by explicit source
replay and `Proof::apply_step`. Bare mid-execution `transport` now searches for
premises, applies the selected simple step once through `Proof`, incorporates
its checked target delta, and retains its source/target spellings and
certificate directly. The former `complete_smart_tactic` construction replay
is gone for this path; snapshot/resource/effect semantics remain centralized
in the same checker used by explicit certificates.

The fifth checkpoint starts migrating direct pure smart goals. `auto` and
`simp` now try checked `Proof` successors for the simple `assumption` and
`normalize` closures. A successful successor retains its own one-step
certificate and avoids the ordinary construction/replay gateway; goals that
need richer simple vocabulary continue through the legacy path for now.
Fully explicit linear pure scripts composed of `apply using`, `assumption`,
and `normalize` use the same checked path.

Direct point-level smart `have` goals now use the same fork-and-apply search
for `assumption` and `normalize`. The accepted successor is wrapped as the
nested `Have` certificate and incorporated directly, without reconstructing
or ordinarily replaying the selected closer.

One-step explicit point `have` bodies using `assumption`, `normalize`, or
`apply using` now check their semantic transition through `Proof` as well.
Their already-simple source certificate remains the enclosing record, so the
migration neither rebuilds nor duplicates it.

The checked proposition vocabulary now also includes the existing
deterministic `intro`, `split`, `left`, `right`, and bounded `enumerate`
operations. Direct pure and point smart closures share a small combinator that
tries these candidates only through `apply_step`; a nonterminal `intro`
strictly removes one outer goal connective.

Explicit `contradiction(fact)` is also checked by `Proof`: the named fact and
its exact negation or opposite condition polarity must both be present in the
persistent fact index before the goal closes.

The explicit `StepUsing` implementation is now one named
`check_step_using` operation rather than an inline tactic-dispatch branch. It
owns premise lowering, exact/effect availability checks, selected fact
transport, statement execution, and the resulting frontier/fact update. This
is the shared audited transition the execution-goal `Proof` slice will call;
explicit source replay already delegates to it.

Bare explicit `step()` now enters that same execution-frontier `Proof` and
submits `StepUsing([])`. It no longer advances `ProofReplayContext` through a
separate mutable dispatcher path; the empty premise list preserves bare
`step()`'s exact-prerequisite and no-automatic-transport semantics, while the
checked successor owns the state, fact delta, and canonical retained step.

Linear smart `step()` plans that select exactly one `StepUsing` now move the
outer execution context into an execution-frontier `Proof`, apply the shared
checker through the ordinary immutable successor API, move the checked
successor back out, and append its retained step. They no longer use
`complete_smart_tactic` or ordinary per-tactic replay. Multi-step and
branching plans remain on the legacy path pending structured proof goals.

Linear `execute()` and `execute_all_paths()` plans composed entirely of one or
more `StepUsing` operations now use the same checked execution `Proof` path.
The proof owns the whole accepted sequence and exports its retained
certificate once; mixed and structured plans still fall back.

Linear `execute_until(...)` plans composed entirely of `StepUsing` operations
also use the execution `Proof`, with the same retained-certificate and
legacy-fallback rules.

Execution-frontier `Proof` now also checks `TransportUsing`, updating the
owned exact fact set and surface lowerings without advancing C. Linear smart
step/execute plans may therefore retain mixed sequences of explicit fact
transports and statement steps; structured steps remain the fallback boundary.

The existing execution-point `UnfoldPredicate` judgment is now one named
`check_unfold_predicate` operation rather than an inline dispatcher branch.
It preserves the current fact rewriting, surface lowering, and contract-entry
derivation behavior. Execution-frontier `Proof` now admits that exact shared
operation, and explicit source replay reaches it through `Proof` as well.
Linear smart execution constructions containing predicate unfolds can retain
them alongside transports and statement steps without an ordinary replay.

`ProofCheckpoint` is an opaque provenance position that retains no semantic
execution state. `certificate_since` accepts only pointer-identical ancestors
from the same checking context and extracts the already-checked suffix in work
proportional to its output. Linear execution uses this path now; branch joins
use the same primitive to embed each arm without inferring it from final
semantic state.

The first audited structural branch is `cases`. `Proof::begin_cases` requires
an exact available disjunction and creates an immutable `ProofBranches` value
whose arms receive only their respective disjunct. Arm steps still go through
`Proof::apply_step`; `join` refuses incomplete arms and embeds each arm's exact
checkpoint suffix in one `SimpleProofStep::Cases`. Explicit pure `cases`
scripts using the migrated simple vocabulary now check through this path, and
regressions cover transactional failed candidates, arm isolation, exact-root
identity, structured certificate output, and expansion through the ordinary
source verifier.

Proof `if` now uses the same branch container. `begin_if` lowers the condition
and its explicit Surface Click negation into isolated arm facts without
requiring either fact beforehand; `join` records one structured `If` step.
Explicit pure `if` certificates over the migrated arm vocabulary recursively
check through `Proof`, including the ordinary independently checked source
path.

The first audited nested scope is pure `have`. `begin_have` creates a fresh
body `Proof` that shares immutable facts and checking context but owns its own
provenance root. Closing an incomplete body is rejected; closing a complete
body publishes exactly its checked proposition and retains its exact nested
certificate in one `SimpleProofStep::Have`. Explicit pure `have` scripts now
use this path. A smart `have ... by simp/auto` whose body closes through the
direct logical vocabulary searches inside that body `Proof` and retains the
successful steps directly, rather than constructing and ordinarily replaying
a second body certificate.

The same direct search path now covers one-node smart pure `if` and `cases`
proofs whose arms close through the direct logical vocabulary. Each arm runs
`try_direct_logical_closure` on its branch-local `Proof`; the join retains
those descendants as the structured certificate. Unsupported richer searches
still fall back to the legacy planner while the shared smart-search vocabulary
continues to migrate.

Point-level `have` now accepts the same structured `If`, `Cases`, and nested
`Have` certificates through `Proof::check_certificate`, rather than limiting
the migrated path to one flat step. Smart point `if`/`cases` bodies with direct
logical arm closures use `ProofBranches` directly. The post-execution outcome
drain also calls this checked branch path against its outcome-specific surface
map without cloning replay state, so these smart bodies no longer fall back to
certificate reconstruction merely because the C execution has returned.

The structural branch representation now has a deterministic multi-size
regression over 16 through 4096 unrelated facts. It counts persistent fact
node allocation around a fixed two-arm `if`, bounds the fork by the tree's
logarithmic height, joins the checked descendants, and confirms certificate
extraction emits only the retained one-node branch. This pins cheap
branch-local fact insertion without relying on wall-clock timing.

Execution-branch preparation has begun at the representation boundary rather
than by wrapping the legacy clone. `SourceExecutionLayout` is immutable after
construction and now stores its statement and loop maps behind one shared
`Arc`; cloning a replay context therefore shares even a 4096-statement layout
by identity. A deterministic regression pins that property. The remaining
mutable replay fields still need separation into persistent semantic state
and legacy certificate/expansion bookkeeping before execution branches can
become cheap `Proof` forks.

The immutable execution-entry fact set is shared as well. It is now an
`Arc<Vec<Proposition>>`, so proof-branch clones do not copy thousands of root
facts; final certification makes the one owned copy it actually extends. A
4096-fact identity regression distinguishes this guarantee from a merely
fast small-corpus clone.

The Proof fact component is now `ProofFacts`: one persistent exact AVL index
paired with the kernel's persistent `PureFactContext`. Point-Proof lowering
accepts that already-indexed context directly instead of rebuilding it by
scanning every available fact for each local step; legacy vector callers keep
their existing adapter. A deterministic 16-through-4096 regression proves
that forks share every assumption-context backing store and one local fact
insertion allocates only logarithmically many exact-index nodes.

Execution proof-case assumptions are now an append-only persistent sequence.
Forking a replay state shares the complete enclosing choice history by
identity, and adding the branch's one local choice allocates one node instead
of copying every ancestor. Ordered iteration remains output-sensitive, and
the certificate-merge path restores the original persistent prefix directly.
This removes the first mutable deep clone from proof-level execution `if`
while the larger execution semantic state continues to migrate behind
`Proof`.

The execution frontier no longer deep-clones the remaining C statement tree
or its continuation stack. Statement-entry and continuation bodies are shared
immutable `Arc<CStatement>` values, while continuations use the same
parent-linked persistent sequence as other branch histories. A branch-local
push and pop changes one stack node and restores the shared ancestor prefix;
a deterministic 16-through-4096 nested-statement regression checks pointer
identity and stack-prefix identity rather than relying on wall-clock timing.
This removes the last source-AST-sized clone from creating an execution branch
before the semantic branch/scope/join operations move behind `Proof`.

Three other branch-local histories now share their complete prefixes as well:
completed C-region markers use a persistent ordered set, and deferred
post-execution work plus deferred expansion path choices use persistent
sequences. Appending one arm-local record no longer triggers a clone of every
enclosing deferred operation. A 4096-entry identity regression checks all
three concrete `TacticReplayState` fields and their one-entry descendants.
The only deliberate contiguous rebuild is the legacy finalization adapter
that edits an already-selected suffix's `surface_recorded` flags.

The execution diagnostic branch path uses the same persistent sequence.
Proof-level and C-level branch exploration now share their complete enclosing
diagnostic path instead of cloning every owned string, while `push`, join-time
`clear`, and ordered error annotation retain their prior behavior. This field
is diagnostic rather than semantic, but removing it prevents otherwise-cheap
semantic forks from retaining a hidden path-depth clone.

Execution-condition preparation now has a `ProofFacts`-native checked path.
It reuses the proof's kernel assumption context, rejects opposite path facts
through a normalized persistent exact index, and appends only the feasible
arm's kernel-issued facts. The kernel condition-fact and signed-order indexes
are persistent AVL maps as well, including real persistent deletion rather
than tombstones, so one arm-local condition no longer clones a complete map
hidden beneath `PureFactContext`. Multi-size allocation regressions cover map
removal, local fact insertion, and a 16-through-4096 condition split. This is
the semantic arm-input operation used by the execution `Proof` branch
container described next.

The first C-execution structural container now owns undecided branches with
empty arms. `Proof::begin_execution_branch` creates only kernel-feasible arm
proofs, retains each condition theorem and path-fact delta, and advances the
two C frontiers without creating detached certificate-builder evidence.
`join_empty` requires both checked descendants at the exact shared
continuation and equal C states, then derives common replay metadata from the
shared root and source branch structure rather than selecting one arm's
metadata. It records one `SimpleProofStep::Branch` atomically. Ordinary source
verification uses this path for an unqualified empty `branch`; selected-source
expansion, decided paths, nonempty bodies, and `ensuring` still use the legacy
driver. A 16-through-4096 fact regression bounds the complete checked
fork/join by logarithmic persistent-node growth and executes the retained
continuation afterward.

Statement certification now exposes the exact facts emitted by the checked
transition as an output-sized semantic delta. Snapshot transports rewrite
that delta while they are already being certified; `step using` therefore
does not rediscover additions by diffing its complete successor against the
ambient context it restores. Execution-frontier `Proof` retains that delta as
`added_facts`, and a 16-through-4096 unrelated-fact regression confirms the
reported statement output is identical at every context size. This is the
arm-local fact input required by the next nonempty execution-branch join; the
statement transition now updates that `ProofFacts` successor persistently as
described below.

`StepUsing` now has a `ProofFacts`-native checked operation. Explicit premise
lowering reuses the persistent kernel assumption context; exact,
materialization-equivalent, condition-polarity, and cross-snapshot
availability use bounded persistent index probes instead of scanning the
ambient context. Snapshot-blind buckets only select same-shape candidates,
which are still decided by the kernel snapshot bridge. The selected successor
facts are inserted by output delta, and persistent prefix batches preserve the
existing semantic order in which transported successor spellings precede
ambient old-snapshot facts. Explicit source `step() using`, smart execution,
and structured execution arms now all enter that operation only through
`Proof::apply_step`; the obsolete vector adapter has been deleted. A
deterministic 16-through-4096 regression checks a fixed explicit statement and
retained certificate under unrelated facts with the original logarithmic
allocation bounds; the complete library expansion suite pins polarity,
snapshot, compound-fact, and successor-order behavior.

`TransportUsing` now uses the same persistent boundary. `ProofFacts` retains
incrementally built restricted contexts for implicit frame facts and direct
surface lowering, so checking one explicit transport neither scans the
ambient fact sequence nor rebuilds a kernel assumption context. Exact premise
selection and target availability use the persistent replay indexes; only a
failing diagnostic materializes the ambient facts. The checked target is
inserted as the operation's local delta, and the now-unused vector checker and
duplicate point-context fact slice were removed. The existing deterministic
explicit-transport curve over increasing unrelated ambient facts now exercises
this `Proof` path directly, while the focused snapshot, materialization,
resource, and expansion tests preserve the transport judgment's semantics.

Execution-frontier `TransportUsing` is now an ordinary forkable
`Proof::apply_step(&self, ...)` operation as well. It clones only persistent
fact and replay roots, records the selected lowerings in the successor, and
leaves the ancestor's C state and provenance reusable for smart-search
backtracking. A multi-size regression retains the transport ancestor and
checks that unrelated C state, certificate history, and effect history remain
shared.

`StepUsing` has now crossed that same boundary. `CState` is a shallow value
whose local, memory, resource, and counted-population storage is internally
shared, so cloning the execution wrapper does not clone complete semantic
state. The checked statement mutates only its successor, the ancestor remains
available for failed-candidate recovery and alternate descendants, and the
separate consuming Proof operation has been deleted. Deterministic multi-size
coverage combines the existing logarithmic fact-allocation bound with direct
ancestor transactionality, repeatable descendant construction, and sharing of
unchanged memory/resource/population storage. The legacy context-export adapter
also accepts a shared checked successor, so retaining a search result cannot
reintroduce a hidden uniqueness requirement.

Explicit `mark` is also a checked execution `Proof` transition now. It records
the named program point only in the returned successor, retains
`SimpleProofStep::Mark`, and rejects a duplicate transactionally without
changing the accepted descendant or its ancestor. The old direct replay-state
mutation has been removed.

Execution `ApplyTheoremUsing` now advances through `Proof::apply_step`. One
canonical point-theorem checker receives the small named premise set as its
complete admissible evidence and borrows the ambient persistent `ProofFacts`
assumptions plus observable resource facts only for lowering. It inserts
conclusions into the persistent successor and returns any standard
function-entry prerequisite/derivation as the same step's explicit delta.
Failed applications leave their ancestor usable; successful applications
retain the exact named step while sharing the unchanged C state and replay
histories. Explicit mid-execution `apply using` and bare smart `apply` both use
this execution Proof transition; the smart form only searches for the premise
spellings first and does not rerun the accepted application. Linear execution
branch arms admit the same step and merge its already-checked deltas through
the existing audited join. A deterministic 16-through-4096 regression proves
logarithmic persistent-node growth, omitted-premise rejection despite ambient
availability, alternate descendants, C-state sharing, structural certificate
retention, and atomic function-entry evidence.

Point-proof `Witness` now advances through `Proof::apply_step` as a local goal
refinement. The checked step evaluates its one explicit witness expression
against the persistent assumption context, replaces the existential goal with
the instantiated body, and retains the exact surface witness in provenance.
Failed names or values leave the ancestor usable. A deterministic
16-through-4096 regression establishes that applying the step does not alter
or allocate nodes in the unrelated fact index; explicit simple `have` scripts
containing `witness` consequently use the ordinary certificate checker backed
by `Proof`.

`Extract` was deliberately not moved unchanged in the witness slice. Its
legacy checker scans the complete available context to find proper
conjunctions and again for every antecedent of a discharged implication.
Since `extract` is a simple step, that implementation violates the efficiency
contract. `ProofFacts` now persistently indexes every strict conjunction
subtree, and `Proof::apply_step(Extract)` uses that index for the exact
proper-conjunct case. Failed extraction is transactional; successful
extraction retains the named step and promotes the conjunct to a top-level
fact with logarithmic persistent work. A deterministic 16-through-4096
regression covers nested conjunctions and distinguishes a proper conjunct from
an independently available fact. Point certificates using this structural
case now cross the Proof boundary.

Discharged-implication extraction now has a persistent consequent index as
well. Each implication chain contributes its explicit antecedent prefixes to
only the exact snapshot-blind keys of its consequents; `extract` selects that
bucket, rechecks the consequent with the kernel snapshot judgment, and checks
each antecedent through indexed replay availability. Independently lowered
universals in the logical/condition fragment use a one-pass alpha key whose
bound variables are structural ordinals and whose free variables retain their
identities. Unsupported quantified atom families produce no broad fallback
bucket and therefore remain on the legacy proof path until their precise key
representation is added. A 16-through-4096 regression grows unrelated
implications while the selected consequent and alpha-equivalent antecedent
buckets remain singleton, bounds persistent allocation logarithmically, and
checks missing-antecedent rejection and ancestor transactionality.

Point-proof `InstantiateUsing` now crosses the same checked boundary. The
selected universal is found through `ProofFacts`' alpha-normal quantified
index and then revalidated by the existing binder-equivalence judgment; named
guards are checked through persistent replay-availability indexes. One shared
deterministic instantiation judgment substitutes the evaluated `int32`
argument, discharges guards from only the explicitly listed premises, invokes
the kernel universal-application rule, and validates its theorem before the
conclusion enters the successor. The legacy point prover delegates to that
same judgment while unsupported quantified atom families retain their legacy
fallback. A 16-through-4096 regression holds one instantiation fixed under
unrelated facts, checks a singleton universal bucket and logarithmic
persistent allocation, rejects an omitted guard despite ambient availability,
and preserves the ancestor and exact retained certificate.

Explicit proposition `Rewrite` now advances through `Proof::apply_step` for
pure and point goals. The rewrite engine accepts an indexed availability
query, so recursively visiting a structured goal no longer rescans the entire
ambient fact vector at every atomic child. `ProofFacts` answers the rule's
exact and direct-load-materialization-equivalent membership without admitting
the broader snapshot or polarity bridges used by other replay rules. The
successor changes only the focused goal and retains the exact surface
equality; failed and alternate descendants leave the ancestor and fact index
unchanged. Existing explicit branch and expansion regressions exercise the
same path, and a deterministic 16-through-4096 regression holds one rewrite
fixed while growing unrelated facts and records zero persistent fact-node
updates.

The simple-step dispatcher now returns one shared `Result<ProofState, _>` and
applies `?` after the match, with large logical and rewrite rules in outlined
helpers. Previously every arm's internal `?` reserved a distinct, large
return temporary, so admitting one more simple step grew the dispatcher stack
frame and made an existing nested expansion overflow. Structured certificate
checking and recursive proposition rewriting use explicit work stacks, so
certificate nesting and proposition depth do not consume the process stack.

Execution `CloseInvariants` is now an atomic `Proof::apply_step` transition.
It checks the loop-region capability, rejects a duplicate transactionally,
sets only the successor's invariant-closure intent, and retains the exact
simple step. Source-position data used solely to attribute the later kernel
bundle check remains attached at the legacy replay export boundary rather
than becoming proof authority. A 16-through-4096 regression holds the step
fixed while growing unrelated facts and records no persistent fact updates.

The execution branch container now accepts linear arm bodies made only of
`StepUsing`, `TransportUsing`, and `UnfoldPredicate`. Each arm advances through the ordinary
checked `Proof` operation and accumulates only its fact and execution-effect
deltas. Predicate unfold also returns its exact persistent-fact,
function-entry prerequisite/derivation, and unfolded-name deltas, so the join
can merge that already-checked metadata without scanning inherited context.
The join embeds each checkpoint suffix directly in the structured
`Branch` certificate, intersects common facts by visiting those arm-local
deltas, unions arm-local certified effects, advances freshness counters, and
reconstructs the common frontier from the shared root. Replay histories that
do not yet have an audited merge rule are rejected by constant-size metadata
checks instead of being selected from one arm. Ordinary verification uses
this path for undecided, no-`ensuring`, linear simple branches; expansion
capture, decided paths, structured/nonsimple arm bodies, and branch
interfaces remain on the legacy driver. A deterministic 16-through-4096
regression measures the join after fixed arm bodies and bounds persistent fact
node growth logarithmically in unrelated context size.

Function-entry execution prerequisites and their kernel derivations now use a
persistent insertion-ordered set. Exact admission and one local insertion are
logarithmic, forks share both the AVL index and ordered history, and final
certification alone materializes the ordered vectors it consumes. The AVL is
one shared `PersistentSet` primitive also used by `ProofFacts`; the earlier
fact-specific duplicate implementation was removed. A deterministic
16-through-4096 regression bounds local node allocation and checks ancestor
isolation, insertion order, and allocation-free duplicate admission.

`SurfacePropositionMap` is persistent as well. Its kernel-to-surface and
surface-to-kernel indexes now share AVL roots across execution proof forks;
recording one new lowering replaces only the logarithmic search paths and the
affected local spelling buckets. The generic `PersistentMap`/`PersistentSet`
implementation lives below the Click language layer and is shared by surface
lowerings, `ProofFacts`, and execution artifact sets rather than introducing
parallel tree implementations. Deterministic 16-through-4096 regressions
bound both raw map updates and complete two-index surface-map updates.

The certificate builder's replay-visible `ProofFactStore` now uses the same
persistent ordered-history plus AVL-index representation. Planning forks share
the complete certificate fact context rather than cloning its vector and tree;
one local insert changes only its persistent suffix and logarithmic index
path. Legacy certificate construction materializes a contiguous vector at its
explicit adapter boundary, making the remaining full-context work visible
until that path is replaced by `Proof` queries.

Frontier-local verified loop clauses and rules are persistent append-only
histories too, so a proof branch after several checked loops shares those
kernel artifacts rather than cloning them. The few legacy APIs requiring
contiguous slices materialize only at loop binding/final export. The old
`frames` set was removed instead of migrated: an audit found that it was
write-only bookkeeping with no semantic or diagnostic reader.

`ProofFacts` now also retains deterministic fact order and a persistent index
from each predicate name to only the propositions that mention it. The
canonical `check_unfold_predicate_facts` judgment consumes this state directly:
it reuses the persistent kernel assumption context, visits only facts indexed
for the requested predicate, and appends unfolded conclusions persistently.
The execution-frontier `Proof` now owns these facts directly instead of hiding
a second mutable `Vec` in `ProofReplayContext`. `UnfoldPredicate` is the first
ordinary forkable execution step: `Proof::apply_step(&self, ...)` checks it
against the indexed facts and returns a successor without consuming or
uniquely owning the ancestor. Unchanged C state, certificate-builder history,
effect facts, planning records, and other legacy replay collections use
explicit clone-on-write sharing while their individual semantic deltas migrate
to persistent representations. A deterministic 16-through-4096 regression
confirms that one selected predicate fact is found without mixing in thousands
of unrelated facts, the ancestor remains unchanged, the retained certificate
is exactly `UnfoldPredicate`, unchanged bulk storage shares identity, and the
local persistent-node work remains logarithmically bounded.

Predicate unfolding now uses that same semantic core for proposition goals,
not only execution frontiers. `ProofState` owns a persistent insertion-ordered
delta of proof-local unfolded predicate names, while inherited point and
execution names remain borrowed from their already-shared contexts. Forks
therefore share the definition environment without rebuilding its history,
and one accepted `UnfoldPredicate` updates only the local delta and the facts
in the selected predicate bucket.
Pure and point goals unfold through `Proof::apply_step`, retain the exact
surface step, and can close from the resulting indexed fact without the
legacy mutable fact vector. The existing execution transition delegates its
fact work to this shared checker and keeps its function-entry artifacts in the
execution wrapper. A 16-through-4096 regression checks singleton candidate
selection, bounded persistent allocation, transactional unknown-name failure,
explicit-certificate checking, and ancestor isolation; a focused point-goal
regression exercises the same retained transition.
A 4096-name regression separately proves that constructing a point `Proof`
allocates no persistent nodes for inherited unfold history.
Point and pure scripts whose smart search is an explicit predicate-unfold
prefix followed by `simp` now apply those unfolds to the same `Proof` and run
the direct logical closer on its successor. The resulting certificate is the
retained path (`UnfoldPredicate` plus the selected simple closer); ordinary
verification does not run the surface-certificate replay gateway. The point
expansion regression independently reparses and checks that retained output.

Point `have` scripts whose smart search is an explicit `witness`/predicate-
unfold refinement prefix followed by `simp` use that same path now. Each
refinement advances the immutable `Proof`, and the direct closer continues
from that checked successor. In particular, the common
`witness(...); simp();` form retains `Witness` plus the selected simple closer
without constructing and replaying another body certificate; its expansion
regression checks the exact retained path and independently verifies the
serialized proof.

Point-proof `Choose` is now a checked refinement too. Function parsing builds
the requirement-label index once, so a named source is not rediscovered by a
linear requirement scan. The successor stores the fresh int32 choice in a
persistent proof-local value map and inserts only the instantiated existential
body into `ProofFacts`; failed labels and duplicate names leave the ancestor
unchanged. Subsequent surface inputs collect the names in their explicit
syntax, probe only those proof-local values, and substitute that bounded set
before ordinary lowering, rather than materializing every preceding choice.
The common smart `choose; witness; simp` path consequently retains its exact
checked `Choose`, `Witness`, and selected closer without construction replay.
A deterministic 16-through-4096 unrelated-fact regression bounds persistent
node growth logarithmically, and the source expansion regression independently
verifies the serialized path.

Point smart theorem application now has a proof-object query seam. The query
lowers only the selected theorem's explicit requirements against the
persistent assumption context, probes `ProofFacts`' exact/materialization
indexes, and returns a concrete `ApplyTheoremUsing`; it cannot insert the
conclusion or edit provenance. The smart `apply(...); simp()` form submits that
step to the same `Proof`, then continues its direct closure search on the
checked successor. Point `ApplyTheoremUsing` is no longer restricted to a root
proof and uses the same persistent-fact theorem checker as execution
application, so an application may follow another accepted refinement without
reconstructing ambient facts. A deterministic 16-through-4096 regression
starts from an extracted predecessor, records zero persistent-index
allocations during candidate selection, bounds application updates
logarithmically, and checks the retained `Extract`/`ApplyTheoremUsing`/closer
path. The source regression confirms that ordinary verification performs no
surface-certificate replay and that expansion independently reverifies the
serialized steps.

Pure smart theorem application uses the same capability boundary now. The
`Proof` query instantiates the applied theorem's own Surface Click requirement
clauses, lowers only those explicit candidates against its persistent
assumptions, probes their availability through `ProofFacts`, and returns one
`ApplyTheoremUsing` without advancing state. This also fixes the former
search/certificate disagreement for a required fact available as a conjunct:
the selected certificate now names the instantiated atomic requirement rather
than the ambient conjunction that happened to contain it. Both
`apply(...); assumption()` and `apply(...); simp()` submit that step once and
continue on its checked successor; the linear scan over every ambient theorem
requirement has been deleted. A deterministic 16-through-4096 regression
records zero persistent-index allocations during selection, and focused
no-replay plus expansion regressions check the retained
`ApplyTheoremUsing`/closer path and independently reverify its serialization.

Pure and point proposition proofs now share one linear smart-script driver on
`Proof` instead of maintaining tactic-shape recognizers in their callers. The
driver pre-recognizes scripts composed of already-admitted explicit
proposition steps, bare `apply`, and a final `simp`; each explicit or selected
step advances the same immutable `Proof` through `apply_step`. This permits a
search to continue across mixed paths such as
`extract(...); apply(...); simp();` without reconstructing intermediate
semantic state or replaying a generated body certificate. Unsupported
structural, execution, and resource scripts remain outside this driver. Pure
and point expansion regressions independently reverify the retained mixed
paths, and deterministic 16-through-4096-fact tests bound the complete fixed
linear script by logarithmic persistent-index allocation.

Audited pure and point `if`/`cases` containers now run that same driver on
each branch-local `Proof`, replacing the former caller-side restriction that
both bodies be exactly `[simp]`. A bare theorem application inside an arm
selects and applies its explicit step against that arm's facts, and `join`
embeds the already-checked descendant certificates. The deferred
post-execution `have` drain recognizes the same structural bodies instead of
requiring their original smart syntax to be a certificate. Point theorem
selection also uses the explicit replay checker's indexed condition-polarity
availability, so an `else` arm's `condition == false` fact can select a
surface `not(condition)` premise without an ambient scan. Pure and point
regressions check no ordinary construction replay, retained
`ApplyTheoremUsing` arms, expansion, and independent verification.

Audited nested `have` scopes now use the linear driver as well. Search inside
the body advances the scope-owned `Proof`; `join` publishes only the checked
proposition and embeds that descendant's exact certificate. The former pure
caller-side loop for “smart have plus selected simple outer steps” has been
deleted, and point proofs use the same path, including recursively nested
smart `have` bodies. An already-simple body inside a surrounding smart script
is checked through the scope's `Proof` rather than treated as planner
metadata. Pure and point regressions retain nested `ApplyTheoremUsing` steps,
observe no ordinary construction replay, serialize the nested scopes, and
independently verify them. A deterministic 16-through-4096-fact regression
holds the smart body fixed, bounds scope search/join/outer closure by
logarithmic persistent-node allocation, and checks that rejected nested
search leaves the original scope untouched.

`If` and `Cases` are now recursive operations of that same script driver,
not root-level cases orchestrated by the pure and point callers. The driver
opens the audited branch container, runs each smart arm on its branch-local
`Proof`, checks an already-simple sibling through that same arm API when a
branch mixes smart and explicit bodies, and joins the retained descendants.
This works at the root or inside arbitrarily nested checked `have` scopes;
fully explicit branches still bypass smart search and remain their own source
certificate. The old pure direct-branch block and point `SmartIf`/`SmartCases`
plans have been deleted. A nested-have/branch/theorem regression expands both
selected arm applications and independently verifies the recursive
certificate.

Post-execution proposition proofs now use that shared driver beyond the
previous branch-only case. A point `Proof` owns the optional checked return
value used by its goal lowering, witness evaluation, rewriting, theorem
selection/application, and fact transport; result-dependent Surface Click is
therefore interpreted by the same immutable object that retains the accepted
steps. The deferred outcome drain asks the driver itself whether a smart
`have` body is wholly supported, then searches and joins that body through
`Proof` instead of duplicating tactic-shape recognition in the caller. A
focused regression applies a theorem to `result` inside such a `have`, checks
that ordinary construction emits no surface-certificate replay, expands the
retained `ApplyTheoremUsing`, and independently verifies it. A deterministic
16-through-4096-fact regression holds that result-aware theorem search fixed
and bounds its persistent-node work logarithmically. Exercising the broader
driver also removed the former root-only guard on point `TransportUsing`:
the shared checker already consumes the current persistent facts, so the step
can soundly follow another accepted refinement and retain both operations.
The copy-segment mdtest and a focused predecessor/transport regression pin
that nested case.

Top-level post-execution theorem application now crosses the same result-aware
point boundary. Bare `apply` asks its outcome `Proof` for one
`ApplyTheoremUsing`, then submits that step once; explicit `apply using`
submits its source step through the identical checker. The outcome drain
incorporates only the accepted step's fact delta and serializes its retained
certificate. The former outcome planner scanned and spelled every available
fact, repeatedly deleted candidates while re-applying the theorem, then
replayed the constructed certificate; those three outcome-only helpers have
been deleted. A 16-through-4096-fact frontier regression records zero
persistent-index allocations during selection, bounds the checked successor
logarithmically, rejects omitted named evidence transactionally, and retains
the exact result-dependent step. The source regression observes no ordinary
surface-certificate replay and independently verifies its expansion.

Top-level post-execution fact transport now crosses that boundary as well.
Outcome-specific premise discovery produces only Surface Click candidates;
bare `transport` tries the corresponding `TransportUsing` steps against one
immutable root and retains the successful deletion-minimized `Proof`
descendant, while explicit `transport using` submits its source step directly.
The outcome drain records the checker-owned source/target lowerings, consumes
only the accepted target delta, and serializes that proof's retained step. The
former outcome helper separately mutated a vector fact context, implemented
transport reachability, inferred premises, and then reran itself to validate
the generated certificate; it and its duplicate planner have been deleted.
The shared checker preserves the deliberate source policy: mid-execution
`using` must establish its logical source explicitly, whereas a completed
return outcome may use the dedicated source slot without duplicating an exact
path fact in `using`. Snapshot materialization now retains its symbolic load
identity by configuring the existing persistent assumption context instead
of scanning or cloning every ambient fact. Regressions cover no ordinary
certificate replay, independent expansion, marked snapshots, certified store
equations, preceding outcome facts, transactional rejection, and logarithmic
persistent allocation for a fixed explicit result-aware transport across 16
through 4096 unrelated facts.

Post-execution predicate unfolding now uses the same result-aware point
frontier instead of mutating the outcome fact vector and separately recording
an `UnfoldPredicate` tactic. The proposition-level unfold transition accepts
an execution-frontier goal as a facts-only refinement, updates only the
predicate-indexed `ProofFacts` delta, retains the exact simple step, and
leaves proposition goals' existing goal-unfolding behavior unchanged. The
outcome drain consumes that checked delta and certificate, while its inherited
unfold-name list remains surface bookkeeping rather than proof authority. A
grouped outcome regression observes no ordinary surface-certificate replay,
and a 16-through-4096 unrelated-fact curve covers result-aware frontier
unfolding, transactional unknown-predicate rejection, logarithmic persistent
allocation, and ancestor isolation.

Grouped post-execution proposition goals now share one immutable result-aware
point-frontier `Proof` context. An audited `focus_point_goal` root operation
selects each externally owned contract goal without rebuilding its persistent
fact indexes or inheriting another goal's provenance. Outcome `assumption` and
`normalize` apply their existing simple steps to those focused roots and retain
the checked certificates immediately; failed candidates leave the shared root
unchanged. A deterministic 16-through-4096-fact regression pins fact-index
sharing and logarithmic local lookup, while a grouped contract regression
requires the two closers to discharge different postconditions without an
ordinary surface-certificate replay.

Outcome `rewrite` now uses those same focused proposition roots. Each open
postcondition submits the named equality as `SimpleProofStep::Rewrite`; only
the accepted successor's rewritten goal is returned to grouped finalization,
and the retained certificate supplies the serialized tactic. The former path
lowered an equality and called the rewrite kernel directly outside `Proof`.
The existing 16-through-4096 equality-index regression pins zero fact-index
mutation and transactional rejection, and a result-finalization regression
checks the retained rewrite/normalize path without ordinary certificate
replay.

Point-frontier `have` scopes are now a checked structural publication
operation for grouped obligations. A completed nested proof inserts exactly
its proved fact into the immutable frontier and retains the nested certificate;
later scopes share that successor and may use the published fact. The audited
`complete_point_obligations` terminal operation then selects every external
contract goal against the accumulated context, applies an ordinary
`Assumption` step to each, and exports the combined retained certificate.
Caller code cannot append unchecked closing syntax. Grouped outcome `simp`
uses this path when its complete open claim set closes through the migrated
direct logical vocabulary, abandoning failed descendants and falling back
without mutation for richer searches. Regressions cover inter-obligation fact
flow, independent expansion/reverification, no ordinary construction replay,
ancestor isolation, and logarithmic work across 16 through 4096 unrelated
facts. Newly stated point goals also lower strictly at the current semantic
point rather than borrowing a same-spelled fact's older snapshot lowering; a
focused regression and the sorted-loop mdtest prevent Proof success from
serializing an `assumption` that explicit verification would reject.

The same grouped path now admits planner-selected proposition candidates,
without restoring the split semantic/certificate architecture. The existing
outcome `simp` planner may propose a supported simple or structured
`ProofCertificate`, but `ProofScope::apply_candidate_certificate` checks that
candidate exactly once through ordinary Proof transitions and retains the
accepted descendant. Grouped finalization observes only the joined successor;
it does not first mutate a goal and then replay the proposed syntax. A focused
rewrite/normalize regression observes no ordinary surface-certificate replay,
expands the retained steps, and independently verifies their serialization.
Loadability, richer existential, and resource candidates still use the legacy
certifiers until their corresponding Proof operations migrate.

Ungrouped exit proposition `simp` with legal top-level existence steps now
uses the same retained obligation path. `choose`/`witness` are applied inside the nested scope
before direct closure, so supported existential goals retain their checked
refinement and closing steps instead of rebuilding and replaying a second
`have`. A focused result-dependent witness regression covers no ordinary
replay, expansion, and independent source verification. Richer existential
plans still fall back after a failed immutable candidate.

Atomic signed-order search now retains its exact selected edge path instead
of exposing only an unordered context-premise set. The certificate layer
consumes that path directly and composes paths longer than two edges through
checked nested `have` scopes and named transitivity applications. This
exposed one remaining pure replay split: the legacy pure executor could not
check a serialized `Have` even though `Proof::check_certificate` already
could. Supported explicit pure certificates now replay through that same
Proof checker, so construction, explicit source verification, and expansion
share the audited scope/application operations. The three-edge regression
expands two retained theorem applications and independently verifies the
result. Other atomic decision kinds remain tracked by the child
atomic-derivation issue.

Resource operations remain a distinct representation prerequisite rather
than being wrapped around the legacy vector APIs. `ResourceContext` currently
stores an `Arc<Vec<CResourceFact>>`; a fork-local insertion or removal uses
copy-on-write on the complete vector and invalidates its lazy complete-context
index, so the next lookup can clone and reindex every ambient resource. A
resource `Proof` transition therefore needs persistent, incrementally updated
exact/shape/block indexes and output-sensitive materialization at the legacy
adapter boundary. Admitting `observe`, resource `unfold`, or `fold` before that
store exists would violate the proof-object efficiency contract even if the
semantic checker were otherwise reusable.

1. Land the canonical vocabulary and a private proof-object core for a small
   linear pure-goal slice. Add deterministic fork/apply scaling regressions.
2. Migrate bare theorem application and fact transport. Their smart forms
   already choose an explicit `...Using` step and are the smallest end-to-end
   proof that search can return the checked successor without independent
   replay.
3. Add typed goal splitting, scopes, and persistent structured certificates;
   migrate logical smart `simp` paths that create subgoals.
4. Migrate smart `step()` so it chooses a concrete `StepUsing` before the
   semantic transition. Remove planning-only statement advancement and
   after-the-fact `ConstructionEvidence` lowering for that path.
5. Migrate `execute`, `execute_until`, `frame`, loops, and `auto` onto the
   shared branch-aware search facilities.
6. Remove ordinary per-smart-tactic independent replay and the obsolete
   reconstruction/building machinery once no smart tactic can bypass the
   proof-object API.

Keep `click expand` and `click audit` independently checking the serialized
rewrite throughout the migration. A migrated smart tactic must continue to
emit a parseable, independently verifiable Surface Click certificate before
its old path is deleted.

The atomic-derivation issue remains a concrete child migration with its own
scaling regressions. The giant nested-memory representation cost in
owned-vector's final certification is separate: the proof-object API should
remove its redundant smart-step check, but must not claim to solve unrelated
deep-term work.

## Regression design

Each migrated vertical slice needs all of these checks:

1. **Provenance by construction:** advancing through a step changes semantic
   state and appends that same `SimpleProofStep`; there is no test-only or
   smart-only successor constructor.
2. **Failure transactionality:** a rejected step leaves the ancestor `Proof`
   unchanged and produces no certificate node.
3. **Backtracking:** several failed descendants can be tried and discarded;
   the selected descendant's certificate contains only its accepted path.
4. **Expansion:** the selected `ProofCertificate` prints, reparses, and
   independently verifies through the explicit expansion gate.
5. **Branch structure:** a split records labeled arms at creation, both arms
   must be discharged, and certificate extraction does not infer the split
   from final contexts.
6. **Scaling:** hold one local step fixed while growing unrelated facts,
   functions, snapshots, goals, and discarded search branches over multiple
   sizes. Fork/apply work follows the deterministic complexity contract.
7. **Capability isolation:** a deliberately malicious test smart tactic cannot
   mint a successor, close a goal, insert a theorem, or edit certificate
   provenance except through the public proof-object operations.

For smart `step()`, retain the owned-vector isolation: the exact generated
`step() using` is a fast simple step, and migrated ordinary verification must
perform that successful semantic transition once. A separate explicit
expansion check must still reject a corrupted printed certificate.

## Acceptance criteria

- The canonical vocabulary above is reflected in Rust type names and
  developer documentation; the old parsed `Proof`/checked `Proof` collision
  does not remain.
- Smart tactics receive `Proof` values with private construction and mutation;
  no smart tactic advances `ProofReplayContext`, `CState`, facts, resources,
  frontiers, goals, or certificate builders directly.
- Every semantic successor is produced by an accepted `SimpleProofStep` or a
  named audited structural operation that records its certificate node
  atomically.
- Every successful smart tactic exposes a structured `ProofCertificate`
  without rule discovery, premise minimization, ambient-fact harvesting, or
  semantic replay during certificate extraction.
- Branching, scopes, joins, and completion are first-class proof-object
  operations shared by tactics rather than reconstructed from final contexts.
- Ordinary verification does not independently re-execute a smart tactic's
  successful simple-step path. Explicit source verification, `click expand`,
  and `click audit` continue to check separately supplied or serialized
  certificates.
- All current smart tactic families are migrated or explicitly blocked from
  using an untracked semantic path; obsolete planning/reconstruction paths are
  deleted rather than retained as fallbacks.
- Deterministic multi-size regressions demonstrate cheap proof cloning,
  local/output-sensitive `apply_step`, discarded-branch isolation, and
  certificate extraction proportional to retained output.
- The full repository gate is green, and the owned-vector smart-step failure
  no longer reports or performs an ordinary per-tactic independent replay.

[`SimpleProofStep`]: ../src/lang/click.rs
