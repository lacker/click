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

Linear smart `step()` plans that select exactly one `StepUsing` now move the
outer execution context into an execution-frontier `Proof`, consume that
uniquely owned proof while applying the shared checker, move the checked
successor back out, and append the retained step. They no longer use
`complete_smart_tactic` or ordinary per-tactic replay. Multi-step and
branching plans remain on the legacy path pending structured proof goals.

Linear `execute()` and `execute_all_paths()` plans composed entirely of one or
more `StepUsing` operations now use the same consuming execution `Proof` path.
The proof owns the whole accepted sequence and exports its retained
certificate once; mixed and structured plans still fall back.

Linear `execute_until(...)` plans composed entirely of `StepUsing` operations
also use the owned execution `Proof`, with the same retained-certificate and
legacy-fallback rules.

Execution-frontier `Proof` now also checks `TransportUsing`, updating the
owned exact fact set and surface lowerings without advancing C. Linear smart
step/execute plans may therefore retain mixed sequences of explicit fact
transports and statement steps; structured steps remain the fallback boundary.

The existing execution-point `UnfoldPredicate` judgment is now one named
`check_unfold_predicate` operation rather than an inline dispatcher branch.
It preserves the current fact rewriting, surface lowering, and contract-entry
derivation behavior. Explicit source replay already uses this shared checker;
admitting the same operation through execution-frontier `Proof` is the next
small transition migration.

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
