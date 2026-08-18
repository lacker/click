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

## Current strategy: continuations and multiple outcome goals

The first migration slices established that `Proof::apply_step` is the right
boundary for a local deterministic transition. They also exposed the next
architectural boundary: a smart tactic often cannot safely select and publish
one locally valid descendant unless the remainder of its candidate proof also
succeeds.

For example, a statement step may be locally valid but discard a fact needed
by a later result proof. An execution branch may admit valid steps in both arms
but fail to establish the interface required by their common continuation. An
opened resource may admit a valid body prefix but fail to close. Execution may
reach several function exits whose path-local `result`, facts, resources, and
effect obligations must all satisfy the remaining script. In each case, the
smart tactic's success condition is a checked continuation, not merely one
checked edge.

Recent migrations have implemented that condition separately at several
sites: resource-scope continuation drivers, branch preflight and join logic,
and complete `execute(); frame();` effect-script transactions. A proposed
execution-prefix/result-suffix bridge for `execute(); simp();` would add
another instance. These slices are useful evidence, but continuing to add
special adapters would reproduce the same missing composition model and keep
returning checked descendants to legacy replay at exactly the boundary that
`Proof` should own.

Pause tactic-family-by-tactic-family migration here. The next implementation
phase is the shared continuation and multi-outcome substrate described below.
Do not add another result-suffix, branch-continuation, or scope-continuation
adapter merely to increase the number of tactics that partially use `Proof`.

### Transactional continuation is untrusted orchestration

The needed transaction is not a new kernel rule, a compound
`SimpleProofStep`, or a second proof representation. `Proof` is immutable, so
speculation is already naturally transactional:

1. retain the unchanged root;
2. apply ordinary checked steps and structural operations to candidate
   descendants;
3. run the candidate's continuation from those descendants; and
4. return a descendant only if the tactic's complete success condition holds.

On failure, dropping the descendants leaves the root unchanged. A partial
descendant is still a sound partial proof, but the smart tactic must not
publish it as that tactic's selected result. "Publish" here means returning a
candidate to the enclosing proof driver and exposing its retained certificate
as the tactic expansion; it does not mean committing a mutable kernel state.

The shared API should make this discipline difficult to get wrong. Its exact
Rust spelling is open, but the semantic shape is a bounded smart-layer
combinator such as:

```rust
attempt(root, |candidate| {
    let candidate = candidate.apply_step(goal, selected_step)?;
    solve_continuation(candidate)
})
```

The combinator may provide `first_success`, `try_sequence`, `solve_each`, and
bounded DFS/BFS facilities. It owns no semantic mutation authority. Every
successor passed through it must already have been produced by
`Proof::apply_step` or a named audited structural operation, and its result is
the resulting `Proof` itself. Diagnostics may retain descriptions of failed
candidates, but a diagnostic record must never become proof authority.

Consequently, no rollback log, mutable transaction context, or independently
checked "candidate certificate" is required. The retained `Proof` lineage is
the certificate. Extracting it after success must perform traversal and
serialization only; it must not rerun the continuation or rediscover any
step.

### `Proof` must own a persistent typed goal collection

Transactional orchestration alone is insufficient while execution exits and
branches are exported as legacy `ProofReplayContext` values. `Proof` must be
able to represent every unfinished judgment created by an accepted
transition, including several simultaneous path-local judgments.

The intended conceptual shape is:

```rust
Proof {
    open_goals: PersistentMap<GoalId, Goal>,
    provenance: ProofNodeId,
}

enum Goal {
    Proposition(PropositionGoal),
    ExecutionFrontier(ExecutionGoal),
    FunctionOutcome(OutcomeGoal),
    Effect(EffectGoal),
    // Additional explicit goal kinds as the audited semantics require.
}
```

This sketch is a capability model, not a mandate for these exact fields or
variants. Goal identifiers must be stable within a proof lineage, and smart
tactics may inspect goal views but not construct, replace, or close goals
directly. Applying one simple step to a focused goal atomically replaces it
with zero, one, or several checked successor goals and records the matching
certificate node. The goal collection and all path-local semantic data use
persistent structural sharing so candidate forks remain cheap.

#### Goal and split identity rules

These rules are normative for the substrate implementation. `GoalId` and
`SplitId` are plain integers allocated from a monotonic counter stored in the
persistent proof state, so the counter forks with the proof and allocation is
O(1).

1. **A `GoalId` names one obligation for its lifetime.** The audited
   operation that creates a goal allocates its id: root construction
   allocates the root goal set, `apply_step` allocates ids for successor
   goals it introduces, and `split` allocates its labeled children plus one
   `SplitId` for the split node itself. A focused refinement that evolves
   the same obligation — a statement advancing an execution frontier, an
   `Intro` peeling a connective — preserves the focused goal's id. Discharge
   retires the id. Whether a step rule preserves or replaces its focused
   goal's id is a static, documented property of that rule, never a runtime
   choice; a rule that changes the goal's kind or count (a return converting
   a frontier into outcome goals, a branch splitting a frontier) retires the
   parent id and records the fresh child ids on its structural node.
2. **Fork preserves identity; nothing else does.** Cloning a `Proof`
   preserves every open goal's id and content. Applying a step to one goal
   leaves every other goal's id and content untouched. Retired ids are never
   reused within the allocating lineage and never reappear.
3. **Comparison is lineage-scoped.** Divergent forks each extend their own
   copy of the counter, so ids allocated after a fork may numerically
   collide across forks. Id equality is meaningful only along one ancestry
   chain or among descendants of the recorded split/scope node whose ids
   they reference. Audited joins verify ancestry first (exact root and node
   identity, as the current containers do); id equality is evidence only
   inside that verified scope. There is no global goal registry.
4. **Join legality is expressed in recorded ids.** A split records its child
   goal ids at creation. `join(split, interface)` is legal only for a proof
   that descends from the recorded split node and has discharged, or brought
   to the declared interface, exactly the recorded child ids. An id not
   recorded by that split can never satisfy its join.
5. **Memoization ignores ids.** Memo keys use semantic proof-state identity
   (facts, goal content, C state), never `GoalId` values or derivation
   history. Two semantically identical states reached along different paths
   may carry different ids and must hit the same memo entry.
6. **Certificate order is recorded order.** An operation introducing several
   goals assigns their ids in the deterministic order fixed by its rule
   (then-arm before else-arm, outcomes in source order) and records that
   order on its structural node. Certificate extraction renders the recorded
   order; it never sorts by id magnitude or discharge order.

An execution step can therefore have these audited outcomes:

- one successor execution-frontier goal for a linear statement;
- several labeled frontier goals for a C branch;
- one or more function-outcome goals when paths return; or
- no successor for a proved non-returning path.

A function-outcome goal owns its path-local result expression, facts, state,
resources, snapshots, and remaining postcondition/effect obligations. A later
`simp`, `have`, `frame`, or explicit simple step focuses those goals directly.
It must not first convert them into mutable replay contexts or re-lower the
semantic aftermath into a new certificate.

The representation must distinguish a valid partial proof from a complete
proof. Completion means that the root's required goal set has been discharged
through checked operations, not merely that one execution cursor reached a C
return statement. Only an audited finalization operation may export the
verified theorem or contract claim.

### Branches, scopes, joins, and continuations compose through goals

Structural operations should transform the same goal collection rather than
running private mini-verifiers that later merge final contexts:

- a split replaces one goal with labeled child goals sharing their prefix;
- a resource open creates a scoped body goal whose checked closure publishes
  only its specified interface;
- a branch continuation is applied to the checked descendant goals selected
  by the branch, not independently replayed after an adapter merge;
- a join checks the explicit branch or scope interface, retains both child
  derivations, and produces the successor goals for the common continuation;
  and
- a function with several return paths retains all outcome goals until the
  required result and effect continuations have succeeded for every relevant
  path.

Some joins are genuine trusted semantic operations, especially where C states
are abstracted or resource interfaces are reconciled. They remain named and
audited proof-object operations. The smart choice to try a join, the order in
which child goals are searched, and backtracking among candidates remain
untrusted orchestration.

The certificate DAG should mirror these operations when they happen. It must
not infer branch ownership, scope boundaries, or continuation order later
from a collection of final states. Common prefixes and continuations should be
shared structurally rather than copied once per outcome.

### What this phase must not become

The continuation substrate must not introduce:

- a `RunContinuation` or other opaque compound simple step;
- a trusted callback whose internal state changes are accepted without
  individual proof nodes;
- a second mutable `ProofTransaction` representation that is lowered into
  `Proof` after success;
- certificate construction from final semantic deltas;
- ordinary replay of a successful candidate for validation;
- conversion to `ProofReplayContext` between execution and result/effect
  goals;
- one special transaction driver per smart tactic or goal kind;
- a multi-goal `apply_step` variant, or any join, scope close, or
  finalization that accepts a caller-assembled goal set rather than the goal
  set recorded by its audited split, open, or root construction; or
- eager cloning of every outcome state, fact set, history, or certificate
  prefix.

If a continuation needs a semantic transition that the current simple or
structural vocabulary cannot express, add the missing explicit checked
operation. Do not grant the continuation an escape hatch around `apply_step`.

### Substrate-first implementation order

The next phase should proceed in independently green substrate slices rather
than additional tactic-specific adapters:

1. Specify and implement stable goal identity plus a persistent typed goal
   collection inside `Proof`. Adapt the existing proposition, point, and
   execution-frontier states without changing their checked semantics.
   Because goals are the only cross-operation currency, `GoalRef` and
   `SplitId` identity across fork and join is load-bearing for three
   consumers at once — join legality, memoization keys, and deterministic
   certificate ordering — so write the precise identity rules down before
   any code, including which operations preserve an identifier and which
   retire it. This step also fixes the two-part operation contract: focused
   `apply_step` may read the whole proof but replaces only its selected
   goal, while goal-set arity exists only in structure-keyed `split`/`join`
   operations (see the intended API shape below).
2. Add shared bounded attempt/continuation combinators over immutable `Proof`
   descendants. Regressions must show that a locally successful prefix whose
   continuation fails returns the unchanged ancestor and publishes no partial
   expansion.
3. Make one execution transition replace its focused goal with its complete
   checked successor goal set, including structural branches. Retain the split
   and any audited join in the proof DAG when they occur.
4. Represent function exits as path-local typed outcome goals. Result and
   effect operations must consume those goals without conversion through the
   legacy replay adapter.
5. Compose branch, resource-scope, and common-continuation search through the
   same goal and attempt interfaces. Add deterministic scaling regressions for
   forks, multiple outcomes, joins, failure discard, and certificate
   extraction.
6. Use complete `execute(); simp();` and `execute(); frame();` scripts,
   including multi-return and resource-sensitive examples, as vertical
   acceptance cases. They must retain one structured checked proof, perform no
   compatibility replay during ordinary verification, and expand into an
   independently verifiable Surface certificate.
7. Migrate the remaining smart-tactic families in groups over this substrate,
   then delete the corresponding planning, reconstruction, and compatibility
   paths. Do not count a family as migrated while its successful path converts
   back to legacy replay before satisfying its continuation.

This order deliberately front-loads the compositional structure even though
it may temporarily move fewer individual tactics. The expected payoff is that
general execution, branches, resources, and function-exit reasoning migrate
together afterward, making the headline acceptance criteria—and deletion of
compatibility replay—realistic.

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

    // Structural split: replaces one goal with labeled child goals and
    // records the split node. `SplitKind` names the audited operation:
    // cases on an available disjunction, a C branch, a scope open, etc.
    pub fn split(
        &self,
        goal: GoalRef,
        kind: SplitKind,
    ) -> Result<(Proof, SplitId), StepError>;

    // Audited join: consumes exactly the recorded split's children. Legal
    // only when every child goal is discharged or at the declared
    // interface; records one structured certificate node.
    pub fn join(
        &self,
        split: SplitId,
        interface: JoinInterface,
    ) -> Result<Proof, JoinError>;

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

1. checks the supplied step against the selected goal and the current proof
   state, including read-only inspection of other open goals where the step's
   rule requires it;
2. creates the successor semantic state and any successor goals, replacing
   only the selected goal; and
3. appends that exact step and its structural outcome to the persistent
   derivation.

There is no successful state transition without matching certificate
provenance and no accepted certificate step that was not checked.

### Focused steps read the whole proof; goal sets come from structure

`apply_step` replaces only its focused goal, but its checker may read the
entire current proof state, including other open goals, as validation input.
This is how inherently multi-goal obligations stay on the ordinary focused
signature: the obligation is reified as a goal in the collection, and the
step focuses that goal. The terminal function frame is the canonical case —
the typed effect goal is a real member of `open_goals`, `FrameUsing` is
applied to it, and its checker ranges read-only over every owned
function-outcome goal before closing only the effect goal. The outcome goals
are untouched and still owe their own result continuations. The already-landed
`FrameUsing` seam behaves exactly this way; this contract codifies it.

Operations that genuinely consume several goals at once — joins, scope
closes, and terminal finalization — are the inverses of splits, and their
goal-set arity is keyed by recorded structure only. `join` takes a `SplitId`,
never a caller-assembled `Vec<GoalRef>`: the member goals and their count
were fixed when the audited `split` recorded them, so a smart tactic cannot
assemble an arbitrary goal set and ask for it to be merged, and a goal from
the wrong lineage cannot be spliced into a join. Terminal finalization is the
root-level instance of the same rule: it consumes the root's required goal
set as recorded at proof construction, not a list supplied by the caller.
There is deliberately no multi-goal `apply_step` variant; caller-chosen goal
sets would be exactly the escape hatch this API exists to close.

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
- a step whose check ranges over several goals it names as input — such as a
  function frame over every owned outcome goal, or a join over its recorded
  child goals — counts those named goals in `q`; it must not visit open
  goals it does not name;
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

The entries below record the independently green vertical slices completed
before the continuation/multi-outcome boundary became clear. They are useful
implementation evidence, not the current priority queue. New work follows
the substrate-first order above; do not resume case-by-case adapters simply
at the end of this chronology.

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
submits the source-distinct `SimpleProofStep::Step`, whose checked transition
delegates to the same empty-premise statement judgment as `StepUsing([])`.
It no longer advances `ProofReplayContext` through a separate mutable
dispatcher path; the empty premise set preserves bare `step()`'s
exact-prerequisite and no-automatic-transport semantics, while the checked
successor owns the state, fact delta, and exact retained source step. The
multi-size statement regression now pins that exact certificate as well as
the existing logarithmic allocation and ancestor-isolation properties.

Linear smart `step()` plans that select exactly one `StepUsing` now move the
outer execution context into an execution-frontier `Proof`, apply the shared
checker through the ordinary immutable successor API, move the checked
successor back out, and append its retained step. They no longer use
`complete_smart_tactic` or ordinary per-tactic replay. Multi-step and
branching plans remain on the legacy path pending structured proof goals.

Linear smart `step()` now searches on `Proof` directly when its complete
premise set is knowable before execution: the statement expression's exact
definedness requirements. The query uses the persistent atomic-reasoning and
surface-spelling indexes to select the requirements' explicit context
premises, then submits one `StepUsing` to the same `Proof`; the C transition
runs only in `apply_step`, and the successor retains that operation as both
semantic state and certificate. The path admits fact-free assignments and
returns, plus signed-overflow cases such as `return x + 1`, but only when those
selected premises are the complete ambient proof-fact set and there are no
effect or resource facts to preserve. Branch and loop frontiers remain on
their structural paths. A rejected candidate leaves the root intact and falls
through to the richer transport planner; deadline failure is not swallowed as
rejection.

Local assignment is the first dependency-indexed exception to the complete-
ambient-set restriction. `SurfacePropositionMap` incrementally indexes kernel
facts by each unanchored current C local in their checked Click spellings. A
smart assignment probes only the assigned name, adds those exact facts to its
`StepUsing`, and leaves every unrelated fact shared in the ancestor. Explicit
`old(...)` and `at(...)` spellings are excluded from the current-local bucket;
if a kernel fact has both current and anchored spellings, selection retains
the current one. The index is persistent, so recording one lowering or
forking a proof copies only logarithmic paths. All three surface indexes live
behind one shared storage pointer, keeping `SurfacePropositionMap` smaller than
its former two-inline-map representation; the deep pure case-split canary
caught the stack regression from initially placing the new map inline.

Focused counter regressions require zero mutable planning transitions for
the empty assignment/return path and the overflow-premise return, and
expansion independently verifies both retained forms. The existing
16-through-4096 unrelated-fact curve requires a generic ineligible query to
reject without allocating persistent fact nodes, and a separate assignment
curve requires successful selection/update to stay logarithmic while sharing
the complete unrelated fact context. A 16-through-4096-name curve also bounds
the local-dependency lookup itself by persistent-index height. Memory writes,
calls, and other statements with unrelated facts still retain automatic
transport planning because a current or later postcondition may depend on
facts that smart `step()` must carry forward. This is the first
execution search path where smart selection operates on proof objects, not
merely where planner output is checked by one afterward.

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
verification and selected-source expansion use this path for unqualified
empty and linear-simple `branch` arms. Structured nodes retain their source
offset, so expansion capture records the exact checked branch delta and then
continues with the still-active capture instead of replaying the branch in the
legacy driver. Decided paths, structural arm bodies, and `ensuring` still use
that driver. A 16-through-4096 fact regression bounds the complete checked
fork/join by logarithmic persistent-node growth and executes the retained
continuation afterward; the selected-source regression also forbids ordinary
surface-certificate replay.

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

The execution branch container now accepts linear arm bodies made of
`StepUsing`, `TransportUsing`, `UnfoldPredicate`, and `ApplyTheoremUsing`, and
can run smart `step()` directly against an arm's owned `Proof`. Each arm
advances through the ordinary checked operation and accumulates only its fact
and execution-effect deltas. Predicate unfold also returns its exact persistent-fact,
function-entry prerequisite/derivation, and unfolded-name deltas, so the join
can merge that already-checked metadata without scanning inherited context.
The join embeds each checkpoint suffix directly in the structured
`Branch` certificate, intersects common facts by visiting those arm-local
deltas, unions arm-local certified effects, advances freshness counters, and
reconstructs the common frontier from the shared root. Replay histories that
do not yet have an audited merge rule are rejected by constant-size metadata
checks instead of being selected from one arm. Ordinary verification uses
this path for no-`ensuring` linear branches, and selected-source expansion
capture reads the retained structural delta. A one-feasible branch is now a
distinct checked path operation rather than a fake join: it validates the
surviving condition theorem and replay metadata, retains the exact descendant,
and records a source-anchored logical `If` whose impossible arm is empty. Its
structural entry step names the deciding surface fact, so independent checking
can re-derive the decision without planner-only fact transport. The legacy
surface builder has an explicit closed-decision bridge, so later steps remain
sequential Proof successors instead of being copied into the impossible arm.
Branch interfaces and structural arm bodies remain on the legacy driver. A
deterministic 16-through-4096 regression measures both joined and decided
paths and bounds persistent fact-node growth logarithmically in unrelated
context size.

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

Pure signed-order `simp` now crosses the theorem-application seam during
search as well. The pure theorem context records each lowered requirement in
the existing persistent `SurfacePropositionMap`; the typed order path selects
only those indexed spellings and proposes a structured certificate of
`ApplyTheoremUsing` and nested `Have` operations. That candidate advances the
same immutable `Proof` through ordinary checked transitions. Its successful
descendant is the returned proof object, so ordinary verification no longer
constructs the signed-order certificate and sends it through `surface
certificate replay`. The three-edge regression now asserts that absence in
addition to expansion and independent verification. Point and execution
atomic derivation consumers, and non-order theory decisions, remain pending.
A deterministic 16-through-4096 unrelated-fact regression also holds that
three-edge proof fixed, checks ancestor isolation and the retained
`Have`/application/closer structure, and bounds its persistent fact updates by
the logarithmic tree height.

Exact ground-int32 equality chains use the same Proof-search boundary now.
The kernel's shared equality graph retains the exact source proposition for
each edge, and its typed derivation exposes the selected orientation. Pure
`simp` converts that path into ordered `Rewrite` steps plus `Normalize`, then
checks the candidate against the current immutable `Proof`; it never first
mutates a semantic goal or independently reconstructs the chain. A three-edge
regression includes a reverse-oriented source equality, observes no ordinary
surface-certificate replay, expands the retained path, and independently
verifies it. Memory-derived equality edges stay with the child
atomic-derivation work.

Point and post-execution outcome `simp` now use that typed atomic-path query
on their own immutable `Proof` as well. Premise spellings come from the
existing exact kernel-to-Surface index; signed paths apply their retained
transitivity theorems through `Proof::apply_step`, and equality paths apply
their retained rewrites through the same boundary. Point theorem application
already completes an exact matching goal, so the path planner explicitly
omits the pure proof's trailing `assumption` instead of submitting a redundant
step. Result-dependent outcome regressions observe no ordinary construction
replay or ambient equality harvest, expand the retained paths, and
independently verify them. Separate 16-through-4096 unrelated-fact curves pin
logarithmic persistent updates for both the point theorem and rewrite paths.
Execution-frontier atomic search and the remaining non-order/equality theory
decisions still require their corresponding typed Proof queries.

The first ten named arithmetic decisions now cross the same boundary. The
kernel retains `Int32IncrementUpperBound` and
`Int32IncrementStrictlyIncreases` evidence, plus
`Int32IncrementBelowMaxIsDefined` evidence for `defined(value + 1)`, with
their exact strict premise. `Int32IncrementLowerBound` is the first
two-premise member: it retains the exact non-strict lower edge and strict
upper edge selected by search. The greater-equal lower-bound,
strict-greater lower-bound, and increment-preserves-order decisions now retain
that same exact pair under distinct typed rule variants. Unrestricted
point/outcome `simp` turns each decision into one checked theorem application
on the current `Proof`.
Standalone pure
`simp() using` now has a restricted Proof query for every currently typed
atomic path. It receives only its explicitly listed Surface premises and
cannot mutate the root while choosing an order, equality, or increment
candidate. Ordinary verification observes no surface-certificate replay,
expansion remains an independent check, and 16-through-4096 unrelated-fact
regressions pin logarithmic persistent work and failed-candidate isolation.
The two-premise family curve additionally rejects either one-premise subset
without mutating the root, then accepts exactly the retained pair for all four
named conclusions.
The two-edge payload is boxed. An initial inline representation enlarged
every atomic-derivation stack frame and deterministically overflowed the
existing deeply branched `sort3` expansion even though that proof never used
the new rule. A representation-size regression now requires multi-premise
evidence to remain behind an indirection, and the existing branch regression
stays green at the normal test-thread stack size.
Contract certification has the matching narrow, fuel-free
`value < INT32_MAX` rule, so a real post-execution definedness contract also
crosses the seam without invoking general arithmetic search.
The rest of the named arithmetic family remains a typed-provenance migration
under the child issue.

Three direct predecessor decisions now use the same theorem-application seam:
positive-to-nonnegative, positive-to-strict-decrease, and the two-premise
nonnegative predecessor upper bound. Exact premise selection uses a bounded
set of persistent-map lookups across comparison orientations, so a coexisting
strict edge cannot displace the non-strict theorem leg. Both pure and point
Proof paths retain only the accepted named application, reject missing
premises without mutating their ancestor, and stay within logarithmic
persistent-allocation bounds from 16 through 4096 unrelated facts. The
outcome path that synthesizes a missing nonnegative leg through equality
rewrites remains separate migration work because its certificate must retain
that nested derivation.

The first such derived predecessor path now crosses the seam without
flattening its intermediate theorem. From an exact `1 <= value` premise, the
smart query constructs a scoped `Have` that applies
`int32_successor_le_implies_lt(0, value)` to establish `0 < value`, then
applies either `int32_positive_predecessor_is_nonnegative` or
`int32_positive_predecessor_strictly_decreases` to the original goal. Every
application and the scope are accepted by `Proof` as they are selected; the
retained structured descendant is the certificate.

Point applications close exact goals immediately at both nesting levels,
whereas the pure form retains explicit `Assumption` closers. The planner now
models that Proof transition directly rather than submitting redundant point
steps. Expansion independently verifies both derived forms, omitted premises
leave the ancestor unchanged, and the common 16-through-4096 unrelated-fact
curve covers the nested structure. Derived predecessor variants that require
equality rewriting, rather than the direct `1 <= value` edge, remain pending.

The two complementary two-premise signed equality decisions now use the same
theorem seam. Search retains either the exact `left <= right` and
`not (left < right)` pair or the exact `left >= right` and
`not (left > right)` pair, selects their Surface spellings through fixed-size
polarity probes, and applies the corresponding
`int32_le_and_not_lt_implies_eq` or `int32_ge_and_not_gt_implies_eq` theorem
once to the immutable `Proof`. Evidence selection uses exact assumed-fact
membership rather than asking the order solver for an equivalent orientation,
so it cannot silently replace the source-supported named rule with its dual.
This closes the common kernel-versus-Surface polarity mismatch without
scanning ambient facts. Pure and point descendants retain only the selected
named application (plus the pure goal's ordinary `assumption`), rejected
premise subsets leave their ancestor untouched, and deterministic
16-through-4096 coverage bounds persistent updates logarithmically. Source
regressions observe no ordinary construction replay and independently verify
the expanded theorem steps.

The two one-premise positive-to-nonnegative decisions now cross the same seam.
From an exact indexed `1 <= value` or `0 < value` source edge, atomic search
retains `int32_positive_is_nonnegative(value)` or
`int32_strictly_positive_is_nonnegative(value)` and submits that application
to the immutable `Proof`; it does not return a bare fact and rediscover the
theorem during certificate lowering. Point and restricted-pure paths retain
the accepted application, rejected premise omission leaves the root
unchanged, and the existing 16-through-4096 single-premise arithmetic curve
bounds both paths logarithmically. Ordinary source verification performs no
construction replay, while expansion independently verifies both serialized
applications.

The exact nonstrict-plus-unequal decision now crosses the theorem seam too.
Atomic search retains the source-supported `left <= right` and
`left != right` facts and submits one `int32_le_and_neq_implies_lt`
application to the immutable `Proof`. Fixed-size polarity probes recover a
Surface spelling for the negated equality without scanning ambient facts.
The point descendant contains exactly that accepted application, the
16-through-4096 unrelated-fact curve bounds its persistent updates
logarithmically, and the pure source regression observes no construction
replay before independently verifying the expansion.

Mid-execution bare theorem application now crosses the same query/transition
seam. The smart form asks its immutable execution-frontier `Proof` for one
concrete `ApplyTheoremUsing`, and only `Proof::apply_step` may add the theorem
conclusion or its provenance. Selection shares the persistent fact indexes
used by point proofs instead of materializing the ambient fact vector through
the legacy premise selector. A 16-through-4096 unrelated-fact curve pins zero
persistent-index reconstruction during selection and logarithmic checked
updates; a source regression observes no ordinary construction replay,
retains the explicit premise, expands it, and independently verifies it.

Loop-invariant initialization theorem search now uses that point theorem seam
as well. The structural point-goal planner no longer rewrites a bare `apply`
by copying every declared theorem requirement into a second, unchecked
`apply using` representation. It builds the invariant's point `Proof`, asks
the shared query for the concrete application, and advances only through
`apply_step`. The loop initialization gateway carries an explicit
`certificate_already_checked` result: when every invariant body was retained
by its successful `Proof`, it uses the corresponding checked fact set directly
instead of independently replaying the generated phase certificate. Explicit
source certificates and smart shapes not yet migrated still take the replay
path. A focused initialization regression observes no ordinary replay,
expands the retained `ApplyTheoremUsing`, and independently verifies that
serialization; the existing 16-through-4096 point-application curve covers
the shared selection and transition path used here.

Default and `by simp` loop-invariant initialization now enter that same point
`Proof` capability boundary before the legacy atomic planner. Direct logical
closure and every already-typed atomic path retain their accepted simple
steps and return the checked invariant fact set to the phase gateway, so they
also skip ordinary replay. Unsupported smart shapes still fall back without
changing diagnostics. The capability query is syntax-only and runs before
constructing the point proof, so fully explicit initialization scripts do not
pay to rebuild persistent fact indexes. A focused assumption-closure
regression checks retained expansion and independent verification; the
existing point-simp scaling curves cover the shared closure implementation.

Automatic execution branches expose a separate structural requirement. A C
branch that reaches distinct function-exit outcomes expands as a logical
`If`, not as the existing equal-state execution `Branch`, so it needs a
Proof-owned multiple-outcome container rather than another flat replay
adapter. `ProgramPointStates` now retains a persistent mutation lineage and
can intersect two descendants relative to their exact common ancestor by
visiting only fork-local changed keys. Its deterministic 16-through-4096
regression preserves shared ambient points, drops arm-specific points, rejects
unrelated lineages, and bounds persistent allocations logarithmically. The
version metadata is boxed behind the map's single pointer-sized value: an
existing deep pure case-split regression caught the stack-cost regression from
an initial inline layout.

The existing execution branch container now consumes that merge for two
checked terminal arms. Each returned execution path carries only the facts
introduced in its own arm, while common inherited facts remain shared in the
enclosing `Proof`; joining therefore does not copy the ambient proof context
per outcome. The join retains a logical `SimpleProofStep::If`, including the
explicit branch-entry steps that independently replay the structural C
transition, and reconstructs the function-exit frontier from the exact shared
root plus audited arm-local metadata. Automatic `execute()` selects this join
for linear simple arms that both return, so ordinary construction no longer
runs the surface-certificate replay gateway for that case. A deterministic
16-through-4096 unrelated-fact regression bounds the terminal join's
persistent fact work logarithmically, and a distinct-return source regression
checks the no-replay path, simple expansion, and independent verification of
the serialized logical `if`. The terminal-join dispatch is outlined from the
recursive executor frame; the existing deep pure case-split canary caught and
now prevents the debug-build stack regression caused by keeping that new
control-flow temporary inline.

Resource operations had a distinct representation prerequisite rather than
being safely wrappable around the legacy vector APIs. `ResourceContext`
stored an `Arc<Vec<CResourceFact>>`; a fork-local insertion or removal used
copy-on-write on the complete vector and invalidated its lazy complete-context
index, so the next lookup could clone and reindex every ambient resource. A
resource `Proof` transition therefore required persistent, incrementally
updated exact/shape/block indexes and output-sensitive materialization at the
legacy adapter boundary. Admitting `observe`, resource `unfold`, or `fold`
before that store existed would have violated the proof-object efficiency
contract even if the semantic checker were otherwise reusable.

The representation prerequisite is now complete. `ResourceContext` is one
pointer-sized immutable snapshot whose stable-ID fact map and exact,
resource, shape, memory-block, endpoint, and concrete-interval indexes are
persistent. Insertion and removal replace only the affected AVL paths; they
do not shift surviving facts or invalidate and rebuild an ambient index. The
ordered `&[CResourceFact]` interface remains as an explicit legacy adapter and
materializes its output once per immutable snapshot. A first inline layout
made recursive execution frames large enough to trip the perpetual-loop stack
canary, so the complete store is shared behind one `Arc`, like the other
persistent proof-state roots.

Deterministic 16-through-4096 regressions cover token exact/shape insertion,
lookup and removal, plus memory exact/block/endpoint/interval insertion and
removal. They require logarithmically bounded persistent-node allocation,
zero allocation for an exact lookup, ancestor isolation, stable ordered
materialization, and shared clone identity. Resource operations can now move
onto `Proof` without inheriting the former context-wide clone/reindex cost.

`observe(resource)` is the first resource operation through that seam. The
shared resource checker now consumes a small indexed fact-store interface:
the checked `Proof` path reuses `ProofFacts`' persistent exact index and
`PureFactContext`, while the remaining legacy resource paths adapt their
ordered vectors at an explicit boundary. Lowering an observation witness no
longer rebuilds assumptions from every ambient fact. One accepted
`SimpleProofStep::ObserveResource` atomically retains the surface step, updated
C/resource state, projected pure facts and surface lowerings, and any
resource-count theorem/prerequisite evidence. Ordinary verification routes
the source tactic through this transition; certificate extraction does not
rediscover or replay the observation. A 16-through-4096 unrelated-fact
regression bounds successful observation work logarithmically and checks
exact certificate identity, ancestor isolation, and failed-step
transactionality. Existing expansion/resource examples independently check
the serialized simple step.

`unfold(resource)` now uses the same indexed seam. Its checked transition
selects the active composite body, removes the folded representation, lowers
and records body facts, materializes the body resources, and retains the exact
`SimpleProofStep::UnfoldResource` atomically. The structural `open` operation
continues to use the same semantic checker through its legacy scope adapter;
there is still only one implementation of the resource law. A separate
16-through-4096 curve checks local persistent work, exact certificate
identity, ancestor isolation, and failed-step transactionality. Initially
placing the second resource transition inline enlarged the recursive replay
driver enough to trip the deep pure-case stack canary; resource-step boundary
export is now outlined in a non-inlined adapter, and the unchanged canary is
green.

Pre-execution `fold(resource)` completes the ordinary simple resource trio on
that seam. The checked transition selects the active body from the persistent
assumption context, verifies each declared pure body fact through indexed
exact/snapshot availability or the maintained kernel context, consumes the
contained resource representation, restores the abstract resource, and
retains exactly one `SimpleProofStep::FoldResource`. Its success path neither
clones nor scans the complete ambient pure-fact sequence; materialization is
reserved for diagnostics and the explicit legacy outcome boundary. A
16-through-4096 unrelated-fact curve checks logarithmic allocation, exact
certificate identity, ancestor isolation, and failed-step transactionality,
and whole-claim expansion independently reverifies the one retained source
step. Post-execution fold remains a distinct outcome/finalization operation;
this migration does not pretend that batch finalization is an ordinary
frontier-local step.

`open(resource) { ... }` now has an audited execution `ProofScope` for linear
all-simple bodies. Scope entry uses the same persistent unfold law in `Open`
mode without serializing a fictitious nested `unfold`; every body operation
advances the child `Proof`; and join either closes the representation at the
current frontier or records the existing deferred close when the child has
returned. The enclosing successor retains exactly one `SimpleProofStep::Open`
whose child certificate is the path that was checked. A 16-through-4096
regression covers entry/body/close allocation, ancestor isolation, failed
entry transactionality, exact nested certificate identity, and both immediate
and return-deferred joins. Ordinary verification now selects this scope for a
linear explicit open body without construction replay, while expansion
independently verifies the serialized scope. Open bodies with structural
branches still use the legacy multi-result driver unless the body is one
checked branch with two feasible linear-simple arms; deeper structural bodies
remain to migrate. The retained-scope probe and its large optional execution
successor are outlined from the recursive structural driver; the unchanged
deep pure-case canary caught the initial stack-frame growth and now pins that
boundary.

Linear open scopes can now incorporate a completed nested `have` as one direct
checked child node. The inner proposition proof borrows the execution Proof's
immutable point snapshot for lowering and indexed theorem selection, but it
cannot advance C execution, open or mutate a resource representation, mark a
point, or close loop invariants. Its join restores the exact outer execution
frontier and publishes only the stated proposition; the outer scope verifies
the child's exact ancestry before accepting it. A source regression selects a
bare theorem application inside `open { have ... }`, observes no ordinary
surface-certificate replay, retains the nested `ApplyTheoremUsing`, and
independently verifies expansion. The existing 16-through-4096 open-scope
curve now includes the nested-scope join, exact nested certificate identity,
and a rejected C-step attempt inside the proposition proof.

The first branch-aware open body now composes the existing audited containers
directly. `ProofScope::begin_execution_branch` opens the C frontier owned by
the scope body, the arm search applies only checked simple steps, and
`join_execution_branch` accepts the result only when its root is the current
body's exact context and provenance node. The outer scope therefore embeds
one retained `Branch` child and later one retained `Open`; it does not infer
either structure from final replay contexts. A source regression covers an
empty C branch inside `open`, observes no ordinary construction replay, pins
the nested certificate shape, and independently verifies expansion. The
checked join now feeds its returned scope body back into the same structural
driver, so a following supported continuation remains on `Proof`; scoped
smart `step()` selects its concrete `StepUsing` on that child and retains the
accepted descendant directly. The regression keeps the return step inside
the scope and pins the resulting `Branch; StepUsing` child certificate.
Scoped branches now also retain a one-feasible `If; StepUsing` child: smart
arm steps use the contextual indexed selector, the scope accepts the decided
Proof as one direct successor, and ordinary verification plus independent
expansion avoid construction replay. Assertions and structural arm bodies
still take the legacy path.

Straight-line smart `execute()` inside an open resource scope now searches on
the scope's checked child `Proof` itself. The indexed statement query selects
one explicit `StepUsing`, submits it immediately through `apply_step`, and the
executor repeats only over the returned descendant; it never advances a
planning clone or reconstructs steps from semantic aftermath. The scope path
is selected only when at least one checked statement reaches function exit,
so unsupported statements and branches still fall back without publishing a
partial descendant. A source regression pins the retained pair of statement
steps, observes no ordinary construction replay, and independently verifies
the expanded scope. The same checked-descendant loop now supports straight-line
`execute_until(statement(N))` inside the scope. The target is resolved as a
read-only proof query, every traversed statement advances through
`apply_step`, and search stops on the retained frontier before the target.
Its source regression combines the smart prefix with a following explicit
scope step, pins their one ordered child certificate, observes no ordinary
replay, and independently verifies expansion. General execute search and
branch traversal remain to migrate.

Execution frontiers now own a typed function-effect goal selection. The goal
is `None`, one effect-clause index for an individual effect proof, or symbolic
`All` for a grouped contract; grouped roots therefore do not copy the whole
claim list each time the legacy boundary creates a short-lived `Proof`. The
selection is preserved by ordinary steps, resource scopes, and both audited
execution joins. A focused regression covers grouped, individual-effect, and
ensure-only proof sites and verifies that a checked successor retains the
same goal. The selection is the target of the audited terminal effect
operation below; it is not copied into the legacy claim list or replay
context.

That terminal seam now exists for explicit function-level `FrameUsing` with
named premises, plus the empty-premise immutable case. `Proof` lowers and
checks only the explicit premise set through persistent fact indexes, checks
every selected effect goal against every owned execution outcome, closes the
typed goal, and retains the exact frame step. Ordered finalization receives a
private checked authority; it performs the resource transition at the
original source position but neither proves the effect again nor emits a
second surface step. A source regression composes `execute`, the checked
frame, and deferred resource-scope close in that order, observes neither
ordinary replay nor the legacy exact-effect-check phase, pins the nested
certificate, and independently verifies expansion. Empty-premise mutable
frames deliberately remain on the legacy path because their current meaning
is “scan all ambient facts,” which is not an acceptable simple-step contract.
Premise-free smart `frame()` now inspects the typed goal, selects an empty
`FrameUsing`, and submits that candidate directly to this operation. This
covers immutable effects and mutable footprints that check exactly from their
declared shape without any pure fact. For a single unpartitioned execution
context, explicitly qualified `frame(function)` now takes the same path. A
failed checked candidate restores the untouched execution frontier before
falling back, so unsupported qualified regions retain their prior diagnostics.
The source regression observes neither ordinary certificate replay nor the
legacy exact-effect recheck and independently verifies the expanded
`FrameUsing` step. Top-level unqualified `frame()` now also searches for and
applies its empty or contextual candidate through this operation before the
compatibility path. Its mutable source regression retains explicit selected
premises, observes neither ordinary replay nor exact-effect rechecking, and
independently verifies expansion. Checked deferred frames carry their retained
certificate to ordered finalization, so an earlier deferred `fold` remains
before the frame without replaying either operation; a source-order regression
independently verifies that expansion. Snapshot-qualified arithmetic theorem
derivations remain on the compatibility path because their recorded lowering
can make theorem application close the live Proof while fresh source still
needs the trailing `assumption`; the existing resource-branch expansion
regression guards that boundary. For a single unpartitioned execution
context, mutable smart frames that need facts reuse contextual footprint
planning only to select a simple candidate, then apply its explicit `Have`
and `FrameUsing` steps once through the owned Proof. Branch-shaped candidates
now use a separate `ExecutionOutcomeProofBranches` container: its arms are
disjoint, exhaustive subsets of the already-checked terminal outcomes, each
path must decide exactly one polarity, and the join accepts only matching
checked effect authority. It restores the complete execution and schedules
one resource transition per original outcome rather than replaying either
arm. The legacy empty-premise source spelling still conflates an explicit
empty set with ambient-fact selection and must not be imported into the
simple checker.

Atomic point `have ... by simp` now asks its nested proposition `Proof` for
the same typed simp closure already used by pure claims and smart scripts,
instead of limiting the owned path to assumption/normalization closure and
then constructing and replaying theorem-backed certificates in the legacy
caller. The selected theorem applications advance only through `apply_step`;
unsupported smart derivations still leave the original replay context
untouched and retain their existing diagnostics. A signed-order regression
requires a composed theorem path, observes no ordinary certificate replay,
pins the expanded `have` as explicit simple steps, and independently verifies
that expansion.

The path-specific regression keeps the original dynamic store
`p[index] = 1` under `index == 0` and the constant store `p[0] = 2` in the
other C arm. Contextual frame construction retains each equality and derived
bound only in the outcome leaf that selected it. Certified-frame lowering now
uses the derivation's exact per-path context rather than the global ambient
fact set, and proposition rewrites inside an execution `have` check through
the nested proposition Proof while the scope join restores the outer
frontier. Verification and the independent expansion gate observe no surface
certificate replay or legacy exact-effect recheck; each performs exactly one
resource transition for each of the two outcomes.

Scoped smart `execute()` now drives a terminal C `if` through the existing
`ExecutionProofBranches` container when both arms are straight-line statement
frontiers. Each arm repeatedly selects and applies `StepUsing`, the terminal
join retains the checked arm certificates, and a following common frame
continues on the joined Proof. `execute` has a distinct indexed selection
policy that carries unrelated facts, memory resources, prior effect facts,
and prioritized successor facts through the checked transition while
selecting only the statement's definedness premises. Standalone smart `step`
retains its stricter explicit-certificate policy. A source regression performs
different array writes in both C arms, crosses the shared return, applies one
common exact frame, pins the `If; FrameUsing` scope certificate, and
independently verifies expansion.

The same scoped `execute` path now recursively opens nested terminal C `if`
frontiers. An inner terminal join becomes the already-checked successor of
its enclosing execution arm, so the outer certificate retains the nested
`If` directly rather than reconstructing it from final outcomes. The outer
arm imports only the inner branch's recorded metadata delta. A second source
regression nests a real array-writing `if` in one outer arm, retains the
nested `If` before one common exact frame, and independently verifies the
expanded proof. Expanded execution-branch certificates are also re-derived
through `ExecutionProofBranches`: the checker validates and consumes the
synthetic branch-entry steps, applies only the retained arm deltas through
simple operations, and compares the resulting condition and arm certificate
exactly before proceeding to a later outcome partition. Structured `if` and
`branch` nodes now retain their source index, so this checked path does not
borrow provenance from either leaf.

The first explicit `branch ensuring` join now belongs to the same structural
API. `ExecutionProofBranches::join_with_interface` checks and abstracts every
continuing arm independently against the declared pure/resource interface,
requires the abstract successor states and exported fact sequence to agree
exactly, and installs the resulting `SimpleProofStep::Branch` atomically. Pure,
non-owning `views`, and exact ownership interfaces cross this seam. The checker
consumes the persistent `ProofFacts` assumption index directly, so it
does not clone or rebuild the ambient fact context. When both arms retain the
same persistent resource snapshot, the join preserves that complete common
context in O(1) and validates only the interface's output-sized additions.
Top-level and scoped linear branches use this path, ordinary verification does
not enter surface-certificate replay, and the retained expansion independently
re-verifies. Rejection leaves the root unchanged, and a deterministic
16-through-4096 unrelated-fact regression bounds persistent allocation by
tree height. A one-feasible interface now validates directly on the surviving
arm without abstraction or resource merging, retains that checked state, and
records a `Branch` with an empty impossible arm; this case can therefore carry
ownership assertions safely. Nested end-of-arm interfaces now derive their
shared frontier by popping the root Proof's persistent enclosing-continuation
stack, exactly as C execution does. Both descendants must share the resulting
stack tail by identity and match its statement index and remaining C
statement; the join retains every enclosing branch completion instead of
trusting one arm's replay state. Ordinary verification of the nested source
performs no surface-certificate replay, expansion independently verifies the
result, and a 16-through-4096 ambient-fact regression bounds the local join
work. A two-arm ownership export also crosses the seam when every owned fact
is already an exact entry in the arms' shared persistent resource snapshot.
The first capability checkpoint lowered only the explicit interface, probed
the exact resource index, and retained that snapshot unchanged. Ordinary
verification and independent expansion cover the source path, while a
16-through-4096 unrelated-resource curve bounds the exact lookup and join.

Differently edited resource snapshots now expose that output-sensitive join.
Every `ResourceContext` retains a persistent origin and exact changed-fact
history; insertion, removal, and real normalization append only touched
representations, while a normalization that changes nothing preserves the
snapshot identity. Given two descendants and their branch root, the common
resource operation visits the union of those local changed keys and removes
from one descendant any exact multiplicity not present in the other. It never
materializes or intersects the unrelated ambient context. Execution branch
arms admit the already-checked resource unfold/fold/observe steps, so the
existing `ready_bundle` regression can consume different path tokens, fold
the same composite in both arms, and retain its `Branch` directly. Structural
preflight is separate from the completed-arm ownership check, so an exported
resource may be established inside the arms. Contextual arm `step()` selects
its explicit `StepUsing` against the owned Proof even when unrelated resources
remain present; the retained arms are exactly `StepUsing; FoldResource`, with
no reconstructed intermediate `have`. A path-sensitive regression counts the
checked source join itself, ordinary verification observes no
surface-certificate replay, and expansion independently re-verifies the
retained arm steps. The contextual selector still refuses a C-advancing step
after an arm reaches the shared continuation, while permitting frontier-local
resource proof steps there; the existing overshoot rejection remains green.
Kernel and complete Proof curves from 16 through 4096 unrelated resources
bound persistent-node allocations for the common-descendant work
logarithmically.

Entailed owned quantities now cross this boundary without global resource
normalization. The join consumes each owned interface fact independently from
both concrete arms, intersects their exact residual descendants, restores the
normalized interface once, and normalizes only the affected exact-resource or
memory-block buckets. This preserves a common quantity-two representation
across a unit ownership interface without duplicating it, while differently
represented arm-only excess is forgotten soundly. The kernel operation tries
direct indexed consumption first and rebuilds only the necessary candidate
bucket when several entries must be combined. A kernel 16-through-4096 curve
holds unrelated resources fixed outside that bucket and bounds deterministic
work and persistent allocation; the corresponding complete Proof curve bounds
persistent allocation. Rejected larger quantities leave the root unchanged. A
source regression counts the checked join, observes no ordinary replay, and
independently verifies expansion. The existing selected-pointer mdtest also
pins the case where one surface ownership interface lowers to different
concrete resources in the two arms and to one common resource after branch
abstraction.

Bare execution theorem application now composes through the same checked
branch and resource-scope containers. Search inspects the selected arm or
scope body's immutable `Proof`, returns one explicit `ApplyTheoremUsing`, and
submits that step to the same descendant; it cannot publish a conclusion or
mutate arm state directly. Function-exit applications deliberately remain
outcome-local until typed outcome goals migrate into `Proof`, because their
surface arguments may depend on `result`. A deterministic 16-through-4096
unrelated-fact curve checks two arm-local searches, logarithmic persistent
updates, rejected-premise transactionality, and exact retained steps. Source
regressions cover both a two-arm interface and a direct application inside
`open`, observe no ordinary replay, and independently verify expansion.

The source-local form of bare execution `transport` now composes through
those containers as well. The arm or scope child tries the empty premise set
and the source proposition's own Surface spelling by applying concrete
`TransportUsing` steps; a success is therefore already the checked retained
descendant. A first prototype enumerated and re-lowered every ambient fact and
took more than 40 seconds at 4096 unrelated facts. That design was rejected,
not hidden behind the fact that transport is a smart tactic. Richer auxiliary
premise discovery stays on the legacy path until it has a relevance index;
the new Proof query never scans unrelated facts. Its deterministic
16-through-4096 curve completes in constant candidate attempts with
logarithmic persistent updates and checks transactional rejection. Branch and
`open` source regressions carry a preserved array fact across a disjoint
store, observe no ordinary replay, retain the exact `TransportUsing`, and
independently verify expansion.

Nested proposition proofs inside execution branches now use the same audited
scope operations as top-level and `open` proofs. `begin_have` roots the scope
at the selected arm's exact current `Proof`; `join_nested` accepts only the
direct completed successor of that same arm, so a checked proof from the
other arm or an earlier arm state cannot be spliced into the branch. The
source executor shares one nested-`have` solver with `open` instead of
constructing a separate semantic aftermath. A deterministic 16-through-4096
unrelated-fact curve bounds two arm-local scopes, checks rejected cross-arm
joins are transactional, and pins the exact nested `Have { Assumption }`
certificates. A source regression retains explicit theorem applications
inside both C arms, observes no ordinary replay, and independently verifies
expansion.

Explicit execution branches whose two arms both end in `execute()` now reuse
the existing checked arm-to-exit search. Every selected statement is applied
to the arm's current `Proof`; the terminal join retains the two exact paths as
one logical `If` and does not reconstruct either arm from returned contexts.
The source selector deliberately requires the symmetric terminal shape:
mixed return/continuation arms still need a typed multi-outcome join and stay
on the legacy driver. The checked branch successor now also owns its supported
linear continuation prefix. Explicit simple operations and contextual smart
`step()` each advance the returned two-arm join `Proof`; a following immutable
effect `frame()` stays on that descendant rather than receiving exported
outcomes. Mutable smart frames remain on the compatibility path until their
path-specific evidence planner consumes the joined Proof state directly.
One-feasible-arm paths retain the already-migrated immediate terminal frame,
but export before an ordinary continuation because the compatibility surface
builder cannot yet preserve its closed branch marker across an unexported
successor. The source-attributed frame adapter lives on `Proof` itself and `ProofScope`
delegates to it, so both paths submit the same empty or planner-selected
`FrameUsing` candidate to the same checked operation. Only after this prefix
has retained its semantic and certificate deltas does the driver export the
descendant and resume the untouched unsupported suffix. A smart miss discards
the candidate and leaves the original context available for the legacy path;
a frame hidden behind an unsupported intervening operation is not claimed by
this slice. One 16-through-4096 unrelated-fact curve includes the two terminal
arm searches, join, and immutable frame and checks an unavailable explicit
frame premise is transactional. A second curve covers a nonterminal arm join,
common return, and frame. Source regressions observe neither ordinary replay
nor the legacy exact-effect recheck, pin the retained branch/statement/frame
steps, and independently verify expansion. Generated certificate suffixes keep
their owning smart tactic's source index, so the continuation driver records
only distinct source continuations; it never publishes a generated suffix as
a second, conflicting expansion of its owning branch.

Bare theorem application now stays on a two-arm branch's common successor as
well. The joined `Proof` performs the same indexed theorem selection used by
arm and scope search, submits the resulting `ApplyTheoremUsing` to itself, and
returns the already-checked descendant before the common statement and
immutable frame. A bounded selection miss discards the candidate branch path
without changing its root; a selected step rejected by `Proof` remains a loud
tooling error rather than triggering compatibility replay. The existing
16-through-4096 nonterminal-join curve now includes a common theorem
application, return, and frame, and checks a missing theorem manufactures no
descendant. A source regression uses a real lower-or-upper C choice, abstracts
the changed local through `branch ensuring`, observes neither ordinary replay
nor the legacy exact-effect recheck, pins the explicit theorem step, and
independently verifies expansion.

The bounded source-local fact transport query now composes on that same common
successor. A two-arm join can retain an entry-snapshot interface fact, select
one explicit `TransportUsing` against the joined `Proof`, and continue through
the common statement and immutable frame without exporting intermediate
contexts. A miss rejects the entire candidate path transactionally, so richer
premise discovery remains available through the unchanged compatibility
operation. The existing 16-through-4096 transport-query curve proves that its
candidate selection ignores unrelated facts, while the nonterminal-join curve
proves logarithmic branch composition. A source regression uses a real
lower-or-upper choice, transports the preserved ordering fact from `old` to
the current snapshot, observes neither ordinary replay nor the legacy exact
effect recheck, and independently verifies the retained explicit certificate.

Nested proposition proof now composes on the common successor too. The
continuation driver opens `Proof::begin_have`, runs the same bounded nested
script search used by branch arms and resource scopes, and publishes the
result only through the scope's checked `join`. The retained `Have` therefore
contains the exact selected theorem application and precedes the common return
and immutable frame on one descendant. The nonterminal-join scaling curve now
includes this nested scope without changing its logarithmic bound. A real-C
source regression proves a selected positive value nonnegative in a common
`have`, checks the retained nested certificate, and independently verifies
expansion. That regression also exposed and fixed the execution/finalization
boundary in independent certificate checking: once the joined Proof reaches
function exit, the continuation driver returns later tactics to the ordered
outcome driver. The checked function frame is the one exception because its
typed effect goal intentionally ranges over every owned outcome; after that
frame, the suffix is outcome-local too. The driver must not try to lower a
later `have result ...` as one proposition on the joined execution Proof,
because `result` is path-local and is intentionally interpreted by each
result-aware point Proof.

Straight-line `execute_until(...)` now stays on that common successor as well.
The bounded search is a Proof operation shared with resource scopes: it
resolves the named frontier read-only, selects each concrete `StepUsing`, and
advances only through the returned checked descendant. The scope adapter
receives the same operation's output-sized fact delta rather than maintaining
a second search loop. A source regression joins a real two-arm selected value,
retains a common nested theorem proof, executes a meaningful checked increment
up to the named return statement, and independently verifies the resulting
`Branch; Have; StepUsing` expansion. Unsupported or branched prefixes still
discard the candidate and resume through compatibility search from the
unchanged root.

Linear `execute()` and `execute_all_paths()` now use the same Proof-owned
search on a common branch successor. The former scope-only loop is one shared
operation: each straight-line statement applies its selected `StepUsing`, and
an encountered terminal C branch composes through the audited execution-branch
container. Search publishes a descendant only at function exit; scope callers
also receive its output-sized introduced-fact delta. A source regression joins
a real positive selection, executes the meaningful common increment and
return, applies the immutable function frame on that same descendant, and
independently verifies the retained statement path. Its claim is deliberately
the immutable effect exercised by this seam. The separate missing typed
certificate for the stronger arithmetic postcondition after the increment is
recorded in `atomic-derivation-returns-premises-not-steps.md` with its exact
reproduction.

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

### Progress (2026-08-16: composed arithmetic theorem proofs)

The pure and point `simp` consumers now retain the first composed typed
arithmetic derivation: from `not (value < 2)` they build a scoped proof of
`value >= 2`, a normalized constant bound `2 >= 1`, and the final
`int32_ge_transitive` application. Every operation advances the same
immutable `Proof`; ordinary verification performs no construction replay,
while expansion independently checks the emitted nested `have` certificate.

Pure theorem application now resolves explicitly named requirements through
the persistent Surface-to-kernel requirement index before lowering them
afresh. This preserves exact-premise checking when Surface Click spells a
canonical false condition as `not (...)`; it does not broaden theorem search
or accept merely derivable ambient premises. A deterministic 16-through-4096
unrelated-fact regression covers both the point and restricted-pure composed
paths.

The same theorem-application seam now covers the direct adjacent-bound rule
`lower + 1 <= value` to `lower < value`. The kernel retains the exact
non-strict source edge, and pure, point, and outcome `simp` submit
`int32_successor_le_implies_lt` directly to `Proof`. This one-step case shares
the same deterministic unrelated-fact curve and expansion check.

Constant lower-bound weakening now crosses the seam too. For
`stronger <= value` proving `weaker <= value`, the kernel retains the exact
stronger source edge and `Proof` checks one `int32_le_transitive` application;
the context-free constant leg remains an internal requirement of that named
simple theorem. The symmetric strict upper-bound form was already covered by
the retained signed-order path's context-free constant tail. Source
regressions now require both forms to avoid construction replay, and the
lower-bound case joins the 16-through-4096 persistent-update curve.

The theorem-application seam now also carries facts proved by one step into a
later step on the same `Proof`. From the exact source `value <= 3`, smart
`simp` checks `int32_le_lt_transitive(value, 3, 5)`, retains its conclusion
`value < 5` in the successor proof state, and then checks
`int32_increment_upper_bound(value, 5)` against that successor. The accepted
certificate is exactly those two applications (plus the pure proof's terminal
`assumption`); ordinary verification neither reconstructs nor independently
replays them. Point and restricted-pure tests pin the structure and bound
persistent allocations from 16 through 4096 unrelated facts.

Symbolic addition definedness now uses the same seam. Given the exact named
theorem premises `0 <= amount` and
`value <= 2147483647 - amount`, smart `simp` selects and checks one
`int32_nonnegative_add_within_max_is_defined(value, amount)` application on
the immutable `Proof`. This was previously a prompt smart-proof failure even
though the explicit simple theorem already existed. The kernel now retains
both selected order edges, including their original reversed Surface Click
spellings; ordinary verification does no construction replay, expansion
independently verifies the application, and a 16-through-4096 unrelated-fact
curve bounds both point and restricted-pure transitions logarithmically.

Symbolic subtraction definedness now follows the identical path. The exact
`0 <= amount` and `amount <= value` edges select
`int32_nonnegative_subtract_within_value_is_defined(value, amount)` and the
application advances the immutable `Proof`. Before this migration the smart
reasoner proved the semantic result but reported that no explicit simple
certificate existed. Reversed source comparisons, no ordinary replay,
independent expansion, omitted-premise transactionality, and the shared
16-through-4096 point/restricted-pure allocation curve are all pinned.

The two operand-order-specific `1 + value` rules now cross the seam as well.
Previously `defined(1 + value)` had a semantic result but no explicit
certificate, while `value < 1 + value` reconstructed the `value + 1` theorem
and then failed ordinary replay because the kernel goal retained the opposite
operand order. Atomic search now records either
`int32_one_plus_below_max_is_defined` or
`int32_one_plus_strictly_increases` together with the exact maximum-bound
edge. `Proof` checks that selected application directly; reversed premise
spelling, no ordinary replay, independent expansion, omitted-premise
transactionality, and the shared 16-through-4096 curve are pinned.

### Progress (2026-08-17: narrow top-level straight-line execution)

Top-level `execute()` and `execute_all_paths()` now first try the immutable
execution-frontier `Proof` for the already-audited exact-context subset. Each
candidate statement advances only through `Proof::apply_step(StepUsing(...))`;
a structural C `if` opens the audited execution branch container, checks both
terminal arms, and joins their exact retained certificates. A successful
sequence exports its already-checked descendant and retained structured
certificate. The obsolete straight-line-only production query has been
deleted. Terminal joins now put the exact positive or negative C path
condition in each arm's entry `StepUsing`, matching decided branches instead
of relying on an enclosing logical `if` as execution authority.

A pending `malloc` success/failure choice is a separate execution split that
the current branch container cannot yet compose with the C-condition split.
Both its capability query and the structural operation itself now reject that
frontier: smart `execute` discards its descendant and resumes compatibility
execution from the unchanged root, while direct misuse cannot duplicate the
Cartesian product of outcomes. The fresh-allocation mdtest pins agreement
between replay and independent kernel certification. The first slice rejected
any inherited unrelated fact, resource,
effect, structural C branch, or unsupported statement transactionally and
restored the pointer-sharing root for the compatibility planner. Standalone
`step()` now also uses the broader checked selector when
the root has unrelated scalar facts: those facts remain structurally shared,
while only exact definedness and current-local dependencies enter the retained
`StepUsing`. Resource contexts still decline this path because their
planner-selected evidence is not represented here. Focused regressions require
zero mutable planning transitions and no ordinary certificate replay for both
the fact-free linear and branched `execute` cases and a scalar-root-fact
`step`. The existing 16-through-4096 execution-branch curve covers the same
fork, arm execution, join, and certificate extraction operations. Top-level
`execute_until(...)` now uses the same exact-root boundary. Its first statement
must not depend on unrelated inherited context; after that accepted step, each
descendant exposes an output-sized `added_facts` delta that the next checked
step can carry without scanning or admitting the root's ambient facts. The
small multi-statement regression now requires zero mutable planning
transitions as well as no ordinary certificate replay.

The repository example gate exposed why this boundary must remain narrow.
`ring_buffer_pipeline` needs a statement-3 memory fact at its later
statement-4 `frame`; that obligation is unrelated to the final return
expression. Selecting facts only by names touched by each current statement
therefore loses a required transport, while selecting every ambient fact
would violate the scaling contract. The broader migration must make execution
search conditional on its next checked obligation (explicit frame premises,
postconditions, or another Proof-owned continuation) and retain only paths
whose continuation succeeds. Until that goal-conditioned search advances
through Proof descendants, memory writes and calls with unrelated facts stay
on the existing planner rather than receiving another local relevance
heuristic. The exact-root `execute_until` slice does not broaden that boundary:
an inherited context it cannot account for still falls back transactionally.

### Progress (2026-08-17: theorem composition with historical locals)

The theorem-application seam now retains a two-rule arithmetic composition
for a post-execution claim. From exact `lower < value` and `value < upper`
facts, smart `simp` first applies `int32_lt_implies_le`, then applies
`int32_increment_strict_greater_lower_bound` on the resulting Proof. The
second simple step consumes the checked fact added by the first; ordinary
verification neither rebuilds nor independently replays the sequence.

Outcome facts that mention a C local after it leaves scope use the Proof's
selected statement-entry anchor. Candidate Surface spellings must lower
directly at the Proof's semantic point before theorem selection accepts them;
an old Surface-index association alone is insufficient authority for theorem
arguments. This keeps spelling recovery within the exact selected fact's
small spelling bucket, and the expanded `at(...)` applications independently
reverify. A 16-through-4096 unrelated-fact curve covers the same two-step
path for point and restricted-pure Proofs.

Post-execution smart `have` now receives that same selected premise anchor.
It retains the nested two-application Proof directly instead of falling back
to the legacy construct-then-replay path when its exact facts name a local
that has left scope.

### Progress (2026-08-17: one-step equality refinement search)

Unrestricted pure `simp` can now refine a legacy atomic decision by trying
each equality from that decision's complete replayable premise set as one
transactional `Rewrite` step on the immutable `Proof`. The accepted rewrite
must be followed immediately by an already-audited direct logical closer or
typed atomic closer; chained equality search remains on the compatibility
path. Search therefore retains `Rewrite; Normalize` directly for the common
`value == 1` proof of `0 <= value - 1`, instead of first deriving the semantic
result and then reconstructing those steps in the surface certificate layer.

The query never scans ambient facts for extra equalities: it visits only the
kernel derivation's selected, replayable premise spellings, and every candidate
advances through `Proof::apply_step`. A 16-through-4096 unrelated-fact curve
pins logarithmic persistent updates, ancestor isolation, and exact retained
certificate shape. A source regression observes no ordinary construction
replay and independently reverifies the expanded rewrite path. Outcome
derivations whose selected historical facts cannot all be respelled, and
multi-rewrite paths, remain explicit compatibility boundaries.

The first structured historical-snapshot case now crosses that boundary too.
For a predecessor upper-bound goal, search keys directly from the goal's
`value - 1` and upper operands, selects only the matching replayable upper
bound and nonnegative-constant equality, and opens a checked nested `have` for
`0 <= value`. The child `Proof` applies the selected equality rewrite and
normalization, its audited join publishes that exact fact, and the successor
applies `int32_nonnegative_predecessor_upper_bound`. The existing `drop_one`
source regression now forbids entry into the explicitly instrumented outcome
compatibility constructor; its expansion independently reverifies the nested
scope and theorem application. A separate 16-through-4096 unrelated-fact
curve pins the point-Proof structure, logarithmic persistent updates, and
ancestor isolation. General historical equality search remains a compatibility
boundary rather than being approximated by an ambient scan.

### Progress (2026-08-17: disjunction elimination on checked branches)

Post-execution `simp` can now eliminate a selected disjunctive requirement
while proving an atomic claim. The proposition derivation records ordinary
disjunction elimination for arbitrary conclusions, and `Proof` opens the
selected Surface spelling with `begin_cases`, proves each branch on its owned
immutable descendant, and joins the retained bodies as one
`SimpleProofStep::Cases`. The grouped outcome certifier accepts that checked
point `have` directly; it no longer requires a flat legacy certificate before
the Proof search can run, nor independently replays the already-checked body.

The motivating `x == 0 or x == 1` proof of `0 <= result` expands to two exact
`Rewrite; Normalize` arms and independently reverifies. Kernel derivation and
contract certification share the same bounded case rule, so proof acceptance
and the independently certified contract frontier agree. A dedicated
disjunction-fact index prevents this broader rule from scanning unrelated
propositions. The 16-through-4096 regression fixes that index at one candidate,
bounds persistent allocations logarithmically, requires exact retained branch
structure, and verifies ancestor isolation. Outcome vocabulary not yet
handled by `Proof::try_simp_closure` remains on the explicit compatibility
fallback.

### Progress (2026-08-17: recursive logical closure on Proof)

Structural `simp` closure now keeps the exact Surface spelling of its current
goal alongside the lowered kernel goal, so implication, conjunction, and
disjunction search can construct their children through the existing audited
`Proof` operations. Implication applies `Intro` and continues on the checked
descendant. Conjunction opens checked `have` scopes for both operands and
then applies `Split`. Disjunction tries each operand transactionally in a
checked `have` scope before applying `Left` or `Right`. Nested scopes receive
their own Surface goal, so these operations compose recursively rather than
returning a detached planner certificate.

Direct post-execution `have ... by simp` and final grouped outcome `simp` now
use this structural search before their compatibility constructors. Source
regressions require the conjunction case to avoid ordinary reconstruction or
replay, expand to the retained named theorem applications and `split`, and
verify independently. A deterministic 16-through-4096 unrelated-fact curve
covers all three connectives, bounds persistent allocation logarithmically,
requires exact certificate structure, and confirms that rejected or selected
descendants cannot mutate their ancestor.

Equality-refinement search no longer discards a replayable selected equality
merely because a different premise in the kernel's semantic derivation lacks
a Surface spelling. It still visits only equality premises selected by that
derivation and advances only by a checked `Rewrite`; it does not trust the
partial derivation or scan ambient equalities. This lets an unfolded
post-execution conjunction prove its historical predecessor leg directly on
`Proof`, and the existing `drop_one` regression now genuinely observes no
outcome compatibility construction.

Pure theorem goals now retain their exact Surface `ensures` proposition when
they enter direct Proof search. Both `ensures ... by simp` and the one-tactic
`ensures ... by { simp(); }` form can therefore use the same recursive
implication/conjunction/disjunction closure as point proofs. The conjunction
regression observes no surface-certificate construction replay, expands both
source forms to the same checked child theorem applications and `Split`, and
independently verifies each expansion. The underlying structural search
continues to use the shared 16-through-4096 persistent-fact scaling
regression.

### Progress (2026-08-17: proposition goals own their Surface view)

`Goal::Proposition` now pairs the checked kernel proposition with an optional
shared Surface Click view inside the immutable `Proof` state. Structural smart
search no longer accepts a caller-supplied goal spelling: it reads the syntax
owned by the same proof whose simple steps it applies. `begin_have` creates a
paired child goal, proposition branches share the complete Surface view by
identity, and `Intro` advances the kernel implication and Surface consequent
together. Goal-changing operations such as rewrite, witness selection, and
predicate unfolding deliberately clear the view when they cannot preserve an
exact corresponding Surface judgment.

This removes the dual `try_simp_closure` / caller-supplied structural closure
interface and lets nested linear smart scripts retain recursive logical
proofs inside checked `if` arms. The pure branch regression expands the owning
`If` to both retained conjunction certificates and independently verifies it.
The existing 16-through-4096 structural curve now also requires every branch
fork to share the root Surface goal allocation by pointer identity.

The production point-level `have` adapter now uses that paired constructor as
well. Previously it lowered the Surface goal and then discarded the spelling
when it created the root `Proof`; the compatibility constructor silently
masked the lost direct path. The post-execution structural-`have` regression
now rejects both compatibility construction and later certificate replay.

Checked proposition `UnfoldPredicate` now transforms the Proof-owned Surface
goal with the same predicate definition while it unfolds the kernel goal and
facts. Consequently `unfold(predicate); simp()` retains the recursive proof
of a predicate-body conjunction instead of discarding the Surface view and
reconstructing a certificate. The existing `ordered_pair` expansion now also
requires ordinary verification to avoid compatibility construction and
replay.

Checked point `Witness` now performs the corresponding capture-avoiding
substitution on the Proof-owned existential Surface goal after the kernel has
accepted and evaluated the witness. A following structural `simp` can refine
an instantiated conjunction on that successor directly. The 16-through-4096
witness curve still requires zero persistent-fact allocation and now checks
the exact Surface body; a source regression expands and independently checks
the retained `witness`, child proofs, and `split` without compatibility work.

Checked proposition `Rewrite` now keeps the kernel rewrite as its sole
authority and treats Surface substitution only as an untrusted spelling
candidate. The candidate is retained when direct lowering at the current
semantic point equals the checked kernel successor exactly; normalized,
historical, or otherwise mismatched spellings are discarded. A 16-through-
4096 conjunction regression requires the accepted rewrite, both recursively
checked child proofs, and `split` to remain one persistent proof lineage. A
pure source regression forbids construction replay and independently verifies
the three retained rewrites and structural join.

### Progress (2026-08-17: qualified frame transition on Proof)

An explicit smart `frame(loop(N))` or labeled loop frame now advances through
one checked `SimpleProofStep::FrameUsing` on the immutable `Proof`. The step
binds the frontier loop clauses already checked by the enclosing loop proof,
uses the shared structural region validator, and schedules the existing
audited `FrameRegion` outcome operation. It retains its exact simple node at
that transition; the replay driver no longer rebuilds the same frame into a
detached certificate and sends it through `complete_smart_tactic`.

The compatibility replay gateway now emits an explicitly attributed operation
event including the tactic and source coordinates. The load-bearing symbolic
loop-bound regression requires the qualified frame not to enter that gateway,
requires its retained `FrameUsing { region: Loop(0) }` node, expands the proof,
and independently verifies the expansion. Label resolution and the missing
loop-effect diagnostic remain covered by their existing regressions. Qualified
frames with explicit `using` premises were initially left on the compatibility
surface; the smart syntax migrated here constructed the exact premise-free
simple step.

Top-level premise-bearing qualified frames now cross the same boundary. The
source `FrameUsing { region: Loop(_), premises }` is submitted directly to
`Proof::apply_step_at`, which lowers every named premise, requires exact
availability across the retained effects, records the simple node, and gives
ordered finalization only checked region-frame authority. This also fixes a
soundness hole in the former deferred adapter: at ordered function exit it
lowered explicit qualified-frame premises but skipped their availability
check, so a contradictory premise could be silently ignored. The regression
requires the available form to retain and independently replay its exact
premise-bearing step, and the unavailable form to fail at the simple Proof
transition.

### Progress (2026-08-18: one theorem-application seam)

Bare theorem application now has one transactional operation on `Proof`
across pure, point, and live execution-frontier contexts. Context-specific
selection may inspect only the immutable proof and returns one concrete
`ApplyTheoremUsing`; the shared seam submits that candidate to `apply_step`
on the same root and returns only the already-checked descendant. Linear
proposition scripts, execution continuations, C branch arms, and resource
scopes delegate to that operation instead of separately pairing a selector
with a state transition. A missing candidate leaves the ancestor unchanged,
while a selected candidate rejected by `apply_step` remains a loud tooling
error rather than permission to retry through compatibility semantics.

The existing 16-through-4096 pure, point, execution, branch, and scope curves
continue to bound selection and persistent updates logarithmically; they now
also exercise transactional misses through the common seam. Function-exit
execution proofs remain an explicit boundary: one such proof may own several
result-sensitive outcomes, so ordered finalization still creates one point
proof per outcome until typed outcome proposition goals migrate into `Proof`.

### Progress (2026-08-18: resource-scoped smart statement steps)

A bare `step()` inside a checked composite-resource scope now selects and
applies its concrete `StepUsing` on that scope's owned `Proof`. Definedness
that follows directly from the resource context no longer needs a fabricated
standalone Surface proposition: the selector probes the explicit empty
candidate through `apply_step`, and a rejection leaves the scope root
unchanged. The checked open-scope driver retains the accepted descendant and
its exact premise list, so ordinary verification neither runs a mutable
planning transition for that source `step()` nor enters compatibility replay.

The existing 16-through-4096 open-scope curve now exercises this smart
selection with unrelated ambient facts and pins the retained `StepUsing`
inside the scope certificate. The snapshot-transport source regression also
attributes planning transitions by claim and tactic, independently verifies
the expansion, and rejects any compatibility replay for its resource-scoped
steps.

This slice deliberately does not broaden standalone top-level `step()` across
an arbitrary resource context. A broader attempt exposed the existing
continuation boundary in `clone_cursor`: a locally valid store can discard a
source-memory fact needed by a later `simp`. The full scope driver searches
its checked continuation transactionally, but a top-level step does not yet
own that suffix. Such a miss therefore continues from the unchanged root on
the compatibility path until continuation-conditioned search is represented
by `Proof`; it is not approximated by harvesting ambient resource facts.

### Progress (2026-08-18: complete linear effect scripts on Proof)

An individual effect proof whose flat script executes to function exit and
ends in `frame()` now searches the complete script on one immutable `Proof`
before publishing any descendant. Every selected statement is retained as
its checked `StepUsing`; the terminal smart frame selects its contextual
`Have` and `FrameUsing` certificate and applies those steps to the same
lineage. If execution, continuation, or frame search misses, the complete
candidate is discarded and the unchanged root remains available for the
compatibility diagnostic. Partial continuations keep their narrower frame
capability boundary.

Memory stores obtain their explicit bounds through source-name indexes. The
selector collects only C variables mentioned by the current statement and
queries the persistent current-variable buckets for those names; it does not
scan unrelated ambient facts. This is enough for a symbolic `p[i] = value`
store to select the `i` bounds and `p` resource fact required by its checked
transition. A deterministic 16-through-4096 unrelated-name curve bounds the
successful store selection by persistent-index height and requires the
retained premise list to exclude every unrelated spelling.

The motivating `execute(); frame();` mutable-effect regression now requires
zero mutable planning transitions and no smart-tactic compatibility replay
during ordinary verification. Its retained simple certificate is still
independently checked by the whole-claim gate and by source expansion, but
that check performs no search: it consumes the already-selected `StepUsing`,
theorem-backed `Have`, and exact `FrameUsing` operations.

The same transaction now covers grouped effect scripts. Contextual frame
selection combines each path's derivations across every selected effect claim
before it applies the single terminal `FrameUsing`; it no longer plans only
the first claim and then discovers during checking that a later claim needs
different evidence. Regressions cover both one grouped mutable effect and two
independently true complete-footprint claims whose symbolic clause requires
an additional bound. Both require zero mutable planning transitions, no
compatibility replay, exact once-only statement steps, and an independently
verified grouped expansion.

### Progress (2026-08-18: substrate 1 — persistent typed goal collection)

`ProofState` now owns `ProofGoals`: a persistent `GoalId`-keyed collection
paired with the lineage-local id allocator, replacing the former single
`goal`/`complete` pair. Roots allocate their obligation's id; goal-preserving
refinement rules (`intro`, `witness`, `rewrite`, goal predicate unfold, and
the frame's effect-selection update) keep it; closers retire it; and
completion is the explicit empty-collection invariant. The normative identity
rules above are the specification this slice implements. A regression pins
fork stability, refinement id preservation, discharge retirement, and forked
sibling isolation. Four allocation regressions now permit the one constant
goal-collection node their operations legitimately write; their bounds remain
independent of proof size.

### Progress (2026-08-18: substrate 2 — bounded attempt combinators)

The untrusted search layer now has one shared combinator module deliberately
outside the audited core: it compiles against the same `pub(super)` `Proof`
surface smart tactics use and owns no semantic authority. `attempt`,
`first_success`, `try_steps`, and `try_sequence` run transactional candidates
from a shared immutable root under a deterministic `AttemptBudget`;
exhaustion is a prompt bounded miss. `candidate_outcome` is the single place
a checked operation's rejection becomes a search miss, so an error raised
with the global deadline exceeded aborts the search loudly instead of
masquerading as one more rejection — previously the shared closure searches
swallowed deadline errors and let them resurface later, misattributed, from
fallback paths.

`try_direct_logical_closure`, `try_simp_closure`, and the structural closure
search now run on these combinators with `Result<Option<Proof>>` signatures
through their production callers; the point/outcome atomic-derivation helpers
retain their internal `Option` idiom behind one deadline check at the `simp`
search boundary until their own migration. Regressions pin: a locally
successful prefix whose continuation fails returns the unchanged ancestor and
publishes no partial expansion; N candidate suffixes over one shared checked
prefix cost N suffix checks with the prefix checked once and only the
accepted path retained; budget exhaustion attempts exactly the admitted
candidates; and the same rejected candidate is a miss without a deadline but
a loud abort with one exceeded.

### Progress (2026-08-18: recorded split identity for proposition branches)

`begin_cases` and proof `if` now allocate a `SplitId` and their labeled child
goal ids together, in rule order, from the root's lineage counter, and each
arm receives its recorded child goal under a fresh entry provenance marker.
The root proof's own collection is untouched until the join commits, so a
dropped split leaves the root the unchanged authority. `join` extracts each
arm's certificate through that arm's exact entry marker: an arm checked under
a different split of the same root — whose numeric ids collide by identity
rule 3 — is rejected transactionally instead of being spliced into the
structured step. A regression pins deterministic rule-order allocation, root
isolation, foreign-arm rejection, and the legitimate join's retained
certificate. The execution branch containers still join through the shared
root checkpoint and migrate onto recorded split identity next.

### Progress (2026-08-18: recorded split identity for execution branches)

`begin_execution_branch` and the terminal outcome partition now allocate the
same recorded split identity: a `SplitId` with rule-ordered child goal ids,
each feasible arm re-keyed to its recorded goal under a fresh entry
provenance marker. The identity lives on the container, never on an arm
value — an early draft stored each arm's marker on the arm itself, and the
new adversarial regression correctly rejected that design by joining a
spliced foreign arm that carried its own credentials. Every join
(`join_terminal`, `finish_decided`, both interface joins, and `join_checked`)
extracts arm certificates through one shared verified operation that requires
the container-recorded goal id and entry marker, so an arm advanced under a
different split of the same root — with identical replay metadata and
colliding numeric ids — fails transactionally. The regression pins that
rejection and that the genuine arms still join afterward.

### Progress (2026-08-18: path-local execution state lives on the goal)

`ProofState` no longer owns an `execution` field. The C execution snapshot —
frontier, replay metadata, branch provenance, and per-step delta — lives on
the goal that needs it: a `FrontierGoal` pairs the effect selection with its
`Arc`-shared snapshot, and a proposition goal stated at an execution point
borrows the same snapshot by identity as its lowering/theorem context,
without any authority to republish a frontier. Ordinary execution successors
go through `replace_sole_frontier`/`replace_sole_execution`, which preserve
the goal's identity and selection while installing the checked snapshot;
discharge drops the goal and its context together. Split arms install their
arm snapshot under their recorded child goal ids. A regression pins the
`have`-body sharing by pointer identity, and one allocation regression now
permits the single goal-map node an execution successor writes. The mdtest
gate caught the one non-mechanical case: predicate unfold and fact transport
are deliberately legal on a nested proposition proof stated at a frontier, so
their successors preserve the goal's kind rather than assuming a frontier
goal; the guarded C-advancing operations keep the strict frontier successor.
This removes
the last shared-state obstacle to a `Proof` owning several simultaneous
path-local judgments; splits producing sibling in-`Proof` goals come next.

### Progress (2026-08-18: goals own their complete path-local context)

`ProofState` no longer owns a fact context either: each goal carries a
`GoalContext` pairing its persistent `ProofFacts` with any borrowed or owned
execution snapshot, so the complete path-local semantics of one judgment now
live on that judgment. Successor helpers preserve goal identity while
installing updated facts (`with_sole_facts`), an updated snapshot, or both;
conditional closers fold their fact successor into the discharge decision;
roots and split arms construct their goals with an explicit context. Fact
queries read through the focused goal, and discharge drops the judgment's
context with it — completed proofs expose only their retained certificate and
output deltas, which is what every production caller already consumed.
`ProofState` retains only lineage-wide data (locals, unfold history, step
deltas, the goal collection). With identity, facts, and execution state all
goal-owned, a split can now produce sibling goals inside one `Proof` without
any shared-state aliasing; migrating the branch containers onto in-`Proof`
sibling goals is the next slice.

### Progress (2026-08-18: the focus cursor addresses one goal per handle)

A `Proof` handle now carries a `focused: GoalId` cursor naming the open goal
it addresses, and every provenance node records which goal its step advanced.
Focus is a cursor, not semantic state: two handles over one persistent state
may address different judgments, checked operations advance exactly the
focused goal, and certificate extraction will partition an interleaved
multi-goal derivation by the recorded per-step attribution rather than
inferring ownership from final states. The `ProofGoals` successors now take
an explicit goal id (`replace_at`, `discharge_at`, `with_facts_at`,
`replace_frontier_at`, and friends), removing the sole-goal assumption from
the collection layer entirely; the single-goal reading survives only in the
`focused_goal` accessor. Two cursor propagation cases were caught by existing
regressions: a decided branch join and an `open` scope close both derive
their successor state from an arm or body whose cursor moved, so the returned
handle addresses that recorded goal id, not the root's. The identity
regression now also pins per-step goal attribution. This is the last
precondition for `Proof::split` producing sibling goals in one state.

### Progress (2026-08-18: typed function-outcome goals exist)

`Goal::FunctionOutcome` is now a real variant, and
`Proof::focus_function_outcomes` is the audited derivation that retires a
function-exit frontier goal (with its effect obligations already closed) and
opens one outcome goal per checked returning path — the first genuinely
multi-goal `Proof`. Each outcome goal owns its path's result value,
post-outcome C state, and fact context (the frontier's facts extended by only
that path's facts), and borrows the frontier snapshot by identity for
lowering; a path proved non-returning contributes no goal. `Proof::goals`
iterates the open set in stable id order and `Proof::focus` moves the cursor
between siblings. The two-arm terminal regression now derives the outcome
set after its checked frame, pins distinct path-local results, snapshot
sharing by pointer identity, sibling isolation, ancestor immutability,
rejection of re-derivation, and a 16-through-4096 allocation curve for the
derivation itself. The next slice migrates the ordered outcome drain to
consume these goals — evolving one persistent result-aware proof per outcome
through its tactics — instead of constructing a fresh point root per outcome
per tactic.

### Outcome-drain migration plan (written 2026-08-18, next work)

The ordered outcome drain (`finish_ordered_proof_replay` and the per-path
per-tactic loop in `claim_proofs.rs`) is the remaining large consumer of the
legacy replay boundary: it receives a `ProofReplayContext`, maintains each
path's working set as a mutable `path_requirements: Vec<Proposition>`
(seventy-plus touch points), and constructs a fresh `for_point_frontier`
`Proof` per outcome per tactic. Typed outcome goals exist; this migration
makes them load-bearing. Stage it as independently green slices:

1. **Entry seam.** The replay engine threads `ProofReplayContext` by value
   through its whole recursion, so do not thread a `Proof` alongside it.
   Instead, the drain head re-enters the substrate once: it already owns the
   final context and every environment `for_execution_frontier` needs, so it
   constructs the terminal execution `Proof` there (effect selection
   `None` — frames are deferred by this point) and derives the outcome goal
   set. This covers checked and wholly legacy execution paths uniformly and
   changes no upstream signatures. Each outcome goal's facts equal the
   drain's current per-path working set by construction (the frontier facts
   plus that path's own facts), which is the parity invariant slice 2
   consumes.
2. **Per-outcome persistent proofs.** For drained paths with an available
   outcome goal, the drain evolves that one result-aware `Proof` through the
   path's tactics: each already-migrated point operation (`unfold`,
   `transport using`, `apply using`, `have`, rewrite, `simp` closures)
   advances the outcome-focused proof, and `path_requirements` for
   still-legacy tactic kinds is materialized from the goal's facts at an
   explicit adapter boundary rather than maintained as parallel state.
   Scouting (2026-08-18) found two prerequisites inside this slice: the
   drain's per-path `outcome_surface_propositions` and `unfolded_predicates`
   evolve tactic-by-tactic alongside the requirements vector, so the outcome
   goal's context must own its surface-lowering map and unfold history (both
   already persistent structures) before any tactic consumes the goal; and
   the point operations read result, pre/post state, premise anchor, and
   surface maps from `PointProofContext`, so they need one goal-aware point
   view that resolves those from a `FunctionOutcome` goal on an execution
   proof. Migrate the view first, then `UnfoldPredicate` as the first
   consuming tactic, with the slice-1 parity assertion extended to hold
   after every consumed tactic, not only at path entry.
3. **Case routing on goals.** Proof-level `if` case assumptions select and
   refine outcome goals through the recorded split structure instead of
   re-deriving membership per path from the requirements vector.
4. **Delete the vector.** When every drained tactic kind consumes the goal,
   remove `path_requirements` and the per-tactic `for_point_frontier`
   constructions; the drain becomes traversal over outcome goals plus the
   ordered resource transitions it already owns.

Each slice keeps the existing drain diagnostics and source-order semantics;
parity is judged by the full gate, and any behavioral difference is a
finding, not an accepted cost. Do not begin slice 2 by adding a second
requirements representation that survives the migration — the goal's
persistent facts are the working set, and the vector dies with slice 4.

### Progress (2026-08-18: drain slice 1 — the head derives outcome goals)

The ordered drain now re-enters the proof-object substrate exactly once, at
its head: the terminal context becomes an execution-frontier `Proof` through
the explicit-selection constructor (`EffectGoalSelection::None` — the
function frame is already deferred checked authority at this boundary) and
derives its typed outcome goal set. A context not at a returning function
exit derives no goals and drains through the legacy path unchanged; no
upstream signature changed. A debug parity assertion in the per-path loop
requires every outcome goal's fact context to equal that path's legacy
working set, and it fired immediately on its first run: the derivation had
included effect-region facts that the drain tracks separately, so outcome
goals now carry exactly the path-local pure facts, with effect facts
remaining on the retained execution snapshot until effect continuations
migrate. The full gate now runs with that assertion live on every drained
path in the corpus. Slice 2 starts consuming the goals: per-outcome
persistent proofs advancing through the drained tactics, with
`available_fact_vector` as the explicit legacy adapter boundary.

### Progress (2026-08-18: the unfold delta is path-local goal state)

The proof-local predicate-unfold delta moved from `ProofState` into
`GoalContext`: sibling goals now unfold independently, which the outcome
drain requires — each drained path evolves its own unfold history. Ordinary
successors preserve the focused goal's delta; both unfold transitions
install their updated delta atomically with their fact and snapshot
successors (`with_context_at`); execution joins merge arm deltas into the
root goal's context through one frontier-checked context update; nested
`have` bodies inherit the parent goal's delta; and outcome goals inherit the
frontier's at derivation. `ProofState` now carries only locals, the goal
collection, and the per-step output deltas.

### Progress (2026-08-18: drain slice 2 begins — unfold consumes its goal)

Post-execution predicate unfolding is the first drained tactic kind to
consume a typed outcome goal in production. The dispatch routes an
outcome-focused proof to the facts-only unfold path — the borrowed execution
snapshot is shared by every sibling outcome and must not absorb one path's
unfolding — and the drain now threads one evolving result-aware proof per
path: the unfold advances that lineage, retains its checked step, and its
per-tactic certificate comes from a checkpoint rather than a fresh root's
whole derivation. The `for_point_frontier` construction at the unfold site
survives only as the fallback for contexts that derived no outcome goals.
The interim resync adapter (`with_drained_outcome_facts`) re-imports the
legacy working set before each migrated tactic while unmigrated kinds still
mutate the vector; each future tactic migration removes its resync, and the
adapter dies with the final drain slice. Head derivation is gated on a
deferred tactic kind that actually consumes outcome goals, so drains with
nothing to consume pay nothing; the gate widens with each migrated kind and
disappears with the final slice. (One `vector-push` gate failure during this
slice was diagnosed per the load-contention rule — the examples suite took
twice its isolated time in the failing run, the isolated re-run and a full
gate re-run both passed on the identical tree — but it prompted the gating,
which is correct regardless.) Remaining for slice 2: the other result-aware
tactic kinds (transport, theorem application, `have`, rewrite, `simp`
closures), whose point views need the goal to own its evolving surface maps
first.

### Progress (2026-08-18: the goal-aware point view; transport consumes it)

`PointOperationView` is the goal-aware point view the slice-2 plan called
for: the point-operation data a result-aware checker consumes, resolved
either from a point proof's borrowed context or from a focused
function-outcome goal — which now owns its surface-lowering map and its
path's effect facts alongside result, state, facts, and unfold delta.
Explicit post-execution `transport using` is the second tactic kind on the
evolving outcome proof: the shared point checker runs against the view, and
the outcome successor records the checker-owned source and target lowerings
on the goal's own map atomically with its fact update — the drain still
records into its caller-owned map only for the benefit of unmigrated
tactics. Smart (premise-searching) transport stays on the legacy path until
its candidate gathering reads the view. The derivation gate now also admits
explicit transports.

### Progress (2026-08-18: explicit theorem application consumes the view)

Explicit post-execution `apply using` is the third tactic kind on the
evolving outcome proof. The point theorem checker now runs against
`PointOperationView` for point proofs and outcome goals alike, and the view
carries the theorem environment. Parity exposed a per-operation distinction
the legacy drain made silently: the transport checker consumes the path's
own execution facts while the theorem checker consumes the replay-level
effect set, so the outcome view resolves its effect-availability context
per operation (`OutcomeEffectContext::Path` versus `::Replay`) instead of
flattening the two. Smart `apply` (the selection query) remains legacy until
`select_theorem_application_step_at_point` reads the view; the derivation
gate admits explicit applications.

### Progress (2026-08-18: smart apply selects on the outcome goal)

The theorem-selection seam that previously refused function-exit execution
proofs — "until outcome proposition goals themselves migrate into Proof" —
now recognizes a focused function-outcome goal as exactly one
result-sensitive point context and runs the shared indexed selection against
the goal-aware view. Bare post-execution `apply` is the fourth drained
tactic kind on the evolving outcome proof: selection reads the view, the
accepted application advances the path's lineage, and the per-tactic
certificate comes from a checkpoint. An unfocused function-exit proof still
returns no candidate, preserving the ordered-finalization seam for paths
that derived no goals.

### Progress (2026-08-18: smart transport searches on the outcome goal)

Bare post-execution `transport` is the fifth drained tactic kind on the
evolving outcome proof. Candidate gathering stays drain-side — it reads the
legacy working set and replay indexes — but every candidate now advances the
outcome-focused proof through the same transactional search used by point
proofs, whose accepted step records its lowerings on the goal atomically.
The search guard recognizes a focused outcome goal as result-aware; the
derivation gate admits all transports. Every post-execution transport and
theorem application in the corpus now runs on typed outcome goals.

The drain rewiring for this slice initially failed silently: a bulk edit
whose pattern had drifted from the formatted source matched nothing, so the
prior commit landed only the search-guard relaxation while the suites stayed
green through the untouched fallback — and the same failure had quietly
narrowed the derivation gate to two tactic kinds. The follow-up commit
completes the rewiring, restores the gate to every migrated kind, and the
process lesson is recorded here: bulk-edit application must be verified by
grep before the claim, because a behavior-preserving fallback makes a
silently unapplied migration invisible to the gate.

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
