# Eliminate prover bugs and legacy proof fallbacks

## Status

This is a P1 tooling blocker discovered while parameterizing the second
adjacent allocation in `examples/arena/arena_second_alloc.click`. The arena C
and the intended ownership claim are ordinary, in-scope uses of Click. The
natural proof repeatedly reached facts that Click had already checked, yet
later proof operations could not cite, serialize, or reverify those facts. A
trivial arithmetic consequence then exceeded the smart-tactic budget, and
profiling the same proof overflowed the process stack.

Stop the parameterized arena work until this issue is reduced and fixed. Do
not weaken the contract, rewrite the C, add irrelevant proof bookkeeping, tune
the proof indefinitely, raise budgets, or merge the broad investigative patch.
The unfinished arena proof is useful as forensic evidence, but the only
regression must not remain in a stash or large example.

The rule for future triage is:

> When a true, in-scope claim has an obvious proof using an existing supported
> operation, and that operation rejects the proof, loses its result, cannot
> serialize it, or cannot reverify it, the failure is a prover bug. Stop proof
> churn and reduce the prover bug.

A prompt, bounded miss by an incomplete smart search remains an automation
limitation when an explicit proof works. That exception does not cover this
session: explicit supported operations lost checked facts; smart search
reported success that its certificate could not express; a small `simp()` did
unbounded unrelated work; and `verify`, certificate construction, and
`profile` did not behave consistently.

No evidence from this session indicates that Click accepted a false theorem.
The observed failures were fail-closed. They are nevertheless correctness and
reliability bugs: a verifier that unpredictably rejects straightforward valid
proofs is not usable for the arena example or larger existing C programs.

## Violated invariant

One checked fact must have one stable semantic identity throughout its useful
lifetime. A proof operation may attach source presentation to that identity,
but source text, a fresh lowering, a memory snapshot, ambient fact order, or a
second execution must never substitute for the identity itself.

In particular:

- a checked kernel transition returns the exact facts it introduced;
- the proof object retains those exact facts and their derivation lineage;
- a Surface Click spelling is a scoped presentation of a checked fact, not a
  key that is allowed to select any equal-looking historical fact;
- quantifier instantiation, resource match/unfold/fold, loop preservation,
  `have`, claim closure, and certificate expansion consume retained checked
  evidence rather than recreating it;
- a smart tactic's successful result is a descendant produced by checked
  proof operations, and expansion serializes that descendant without semantic
  reconstruction;
- independent certificate checking follows the serialized checked operations
  and reaches the same result without smart search, ambient scans, repeated
  execution, or legacy certification; and
- explicit simple steps do work proportional to their explicit inputs and
  produced proof-state delta, not to unrelated path history or ambient facts.

The current architecture states much of this contract in
`docs/internals/proof-objects.md`, but active proof paths still cross seams
where exact evidence is replaced by reconstructed presentation or by a legacy
checker. The implementation and the documented model therefore disagree.

## Root cause

This is not seven unrelated prover algorithms failing at once. The common root
cause is an incomplete migration from reconstruction-based proof checking to
one persistent checked proof object.

The semantic half of the new design exists: kernel operations can return
checked descendants, persistent facts, typed execution evidence, and retained
branch lineage. But the complete end-to-end identity of an introduced fact is
not carried through every consumer. Surface presentation, resource adapters,
loop planning, smart `have`, claim certification, and certificate expansion
still contain older paths that expect to recover meaning later from structural
proposition equality, source spelling, fact-vector order, a newly lowered
snapshot, or a second checker.

That split creates one recurring failure sequence:

1. the kernel proves or exposes the right fact;
2. an API carries the proposition value but drops some of its provenance,
   binder, snapshot, selected-path, or source-clause correspondence;
3. a later Surface or certificate consumer tries to reconstruct the dropped
   relationship;
4. reconstruction works in simple tests but becomes ambiguous after a loop,
   resource match, unfold, instantiation, or memory update creates another
   equal-looking fact; and
5. a legacy fallback searches more ambient state, takes a different proof
   route, times out, or produces a certificate different from the checked
   proof.

The fallbacks allowed the migration to look complete one path at a time. They
masked missing evidence instead of forcing an incomplete producer/consumer
contract to fail at its boundary. Local regressions consequently exercised
resource facts, loop invariants, arithmetic, or expansion in isolation, while
the arena allocation composed all of them and crossed the fault line several
times.

There is also a representation mismatch underneath the migration. Kernel facts
are structurally represented propositions containing generated variables and
snapshot-relative loads; Surface proof steps are generally recovered through
human-readable propositions. Structural kernel equality is too specific to
survive legitimate presentation changes, while Surface text equality is too
weak to distinguish historical facts. Without a retained scoped identity and
checked presentation relation, every bridge is forced to guess in one
direction or the other.

So the system has accumulated architectural debt in this area. It is not
evidence that every kernel rule is unsound or that the entire verifier is
decaying uniformly. It is evidence that the proof-object migration stopped at
an unsafe halfway point, compatibility paths kept the old model alive, and
composition coverage was insufficient to expose that fact promptly.

## What went wrong in the arena session

### Bugs fixed on the way to the parameterized allocation

The feature work had already exposed a succession of independent prover bugs.
These landed fixes are evidence of the systemic boundary problem, not a list
of proof tricks that should be repeated:

1. Applications of `int32_add_nonnegative_right_is_at_least_left` and
   `int32_increment_upper_bound` succeeded locally but did not retain their
   kernel derivations for whole-function certification. The focused regression
   is `mdtests/region_relative_index_read.md`.
2. A speculative alias guard survived a failed nested search and was accepted
   by fast cell lookup even though compact resource composition proved the
   cells separated. The result was a spurious type mismatch in `arena_read`.
3. `arena_write` verified through one execution path, then a hidden second
   whole-function execution failed to reproduce the resource path. Retaining
   typed execution evidence removed that repeated execution.
4. A child selected by `unfold(parent) as { slot: child }` initially carried
   only a provisional parent family, so a loop binder could not take over the
   child under the family declared by the selected arm.
5. Model bindings introduced by a proof `match` disappeared while lowering a
   nested proof `if` inside `preserve by`.
6. Matching an exactly named resource model did not publish checked
   binding-dependent quantified facts from the selected resource arm.
7. Stable loop invariants were reconstructed with suffix and membership
   guesses instead of being paired with the transition's exact introduced
   fact delta.
8. Early-return postcondition lowering could choose the wrong conditional
   lowering candidate instead of the unique candidate whose routing facts
   were checked at that outcome.

Each repair made the arena proof advance to another identity or reconstruction
seam. That pattern should have triggered this reduction earlier.

### Unresolved failures in the parameterized adjacent allocation

The next natural proof exposed all of the following in one composition:

1. **Conditional resource-body lowering was treated as unsupported.** A named
   resource fact could lower to multiple conditional paths even when the
   retained assumptions uniquely selected one fully discharged path. Resource
   rewriting required a raw singleton rather than using the kernel's checked
   path selection.
2. **Later resource facts could not depend on earlier resource facts.** Facts
   were lowered in declaration order, but the exact earlier result was not
   added to the assumptions used for the later fact. A quantified memory fact
   whose bound followed from the preceding scalar fact was therefore rejected.
3. **Resource unfold discarded exact fact presentation.** The kernel exposed
   exact checked body facts, but later Surface proof steps attempted to lower
   the declaration text again against a materialized snapshot. The new
   lowering minted distinct load identities.
4. **Explicit quantifier instantiation produced an unusable conclusion.** The
   instantiated universal fact retained its declaration-time registered load,
   while the focused goal named the corresponding load in the current
   snapshot. The prover knew enough to establish the fact but could not use it
   to close the goal.
5. **Loop invariant identity was reconstructed from text.** Preservation
   planning re-lowered invariant source instead of retaining the exact
   loop-head facts returned by invariant checking. An older resource fact and
   the current loop invariant could have identical source spelling but
   different kernel loads.
6. **Unqualified surface lookup selected stale evidence.** During certificate
   construction, a retained exact premise such as `(i + 1) <= capacity` was
   paired with its source presentation, but the surface map selected an older
   fact with the same spelling instead of the exact premise in the pair.
7. **Smart success was not serializable as a checked certificate.** Local smart
   reasoning advanced, then certificate lowering reported that its surface
   premises did not express the atomic derivation. The proof object had not
   prevented a successful checked descendant from reaching a certificate seam
   that tried to rediscover its meaning from source text.
8. **A trivial mid-execution `have` was catastrophically expensive.** The
   proof timed out on `have i <= prefix and run_length == 0 by simp`. Profiling
   attributed about 18 seconds to smart work, about 66,110 snapshot rewrite
   calls, and roughly 1.27 million units of contract-`have` checking work.
   Those costs were unrelated to the size of the stated consequence.
9. **A one-edge arithmetic rule searched unrelated transitive context.** The
   `int32_increment_upper_bound` rule searched for an arbitrary signed-order
   path and then accepted only a singleton path. A rule with one named direct
   premise therefore scaled with unrelated order facts.
10. **Fixing that lookup only moved the timeout.** After using the direct edge,
    the prover stalled on the next trivial consequence,
    `prefix != capacity` from `prefix < capacity`. The problem is broader than
    one arithmetic rule.
11. **Profiling overflowed the stack.** `click-profile` on the same proof
    overflowed its process stack while traversing or constructing the smart
    proof. A diagnostic tool must not crash on the proof whose performance it
    is meant to diagnose.
12. **A second proof route did not restore a coherent boundary.** An experiment
    that routed mid-execution smart `have` through the native
    `begin_have -> try_simp_closure -> join` operations still timed out and
    still led to profile stack overflow. It was reverted. Adding another
    adapter around the same reconstruction model is not the fix.

The investigative patch grew to thirteen source files and approximately 333
changed lines, spanning resource lowering, proof facts, loop contexts,
surface maps, certificate lowering, and arithmetic reasoning. It must not be
merged as a bundle of local bridges. Its breadth is evidence that the wrong
abstraction was being repaired at every consumer.

## General bug classes exposed

### 1. Checked fact identity is replaced by source equality

Surface proposition text is not a semantic identifier. The same spelling can
refer to a resource-entry load, a loop-head load, a current-state load, or a
snapshot-qualified load. Conversely, one checked fact can have several valid
surface presentations. A global or nearest-looking text map cannot safely
represent either relationship.

This caused stale selection, ambiguous invariant citations, resource-unfold
load mismatches, and certificate premises that no longer denoted the exact
derivation input.

### 2. Snapshot-relative values are reminted at subsystem boundaries

Resource lowering, loop planning, instantiation, goal lowering, surface
synthesis, and certificate construction can independently create symbolic load
terms for the same program read. Equality provability is not a general
replacement for stable identity: the proof may need a specific binder,
snapshot, resource-contained read, or derivation premise.

The system needs explicit checked transport when a fact is intentionally
presented at another snapshot. It must not silently rely on fresh lowering or
ad hoc operand-equivalence bridges.

### 3. Proof producers return less evidence than consumers need

Several APIs return a new state or a bag of propositions but omit the exact
ordered correspondence between source clauses, selected conditional paths,
introduced facts, binders, and derivations. Consumers then infer that
correspondence from order, membership, source spelling, or ambient context.

This is the common shape behind the resource-body, stable-invariant,
early-return, and certificate-pair failures.

### 4. Presentation code is still performing semantic recovery

Certificate construction and expansion should serialize retained checked
operations. Instead, some paths re-lower source propositions, synthesize a
spelling and re-lower it, reconstruct a state, search available facts, or run a
parallel certifier. Presentation then becomes a second prover whose choices
can disagree with the proof that actually succeeded.

### 5. Smart and explicit proof paths do not share one end-to-end object

The proof-object design correctly requires smart search to produce checked
descendants. The arena failure shows that this guarantee stops too early: the
descendant's semantic facts and the data later needed to serialize those exact
operations are not uniformly the same retained object. “Smart succeeded, but
the certificate cannot express its selected premise” must be impossible by
construction.

### 6. Ambient context is being used as an implicit API

Rules that need one premise search transitive order graphs, scan fact vectors,
rewrite many snapshots, or ask a general prover to rediscover an already
selected fact. Besides making identity ambiguous, this violates the scalable
verification contract. Adding unrelated facts must not change which exact
premise is selected or make a simple step time out.

### 7. Recursive construction and checking are not stack bounded

The profile stack overflow shows that a legal proof shape can drive recursive
smart-proof or certificate traversal past the process stack. This is a tooling
reliability bug independently of whether ordinary verification also times out.
The checked path, expansion path, and profiler must use bounded-stack traversal
for user-controlled proof depth and generated certificate structure.

### 8. Feature work lacked a hard prover-bug stop rule

The process failure compounded the implementation failures. Each time the
obvious proof was rejected, the session added another local adaptation and
retried the large proof. The correct response was to reduce the first failure,
classify it, and repair the producer/consumer contract before resuming arena
work.

## Legacy fallbacks are part of the bug

Active proof-authority fallbacks are bugs waiting to bite this same seam. A
fallback is unacceptable when failure to retain exact checked evidence causes
the implementation to:

- invoke a remaining legacy certifier or pure-proof driver;
- rebuild a legacy fact vector or resource view;
- re-execute or reconstruct a function prefix, entry, exit, or loop state;
- re-lower a source proposition and treat a matching result as the original
  fact;
- synthesize source text and re-lower it to recover a certificate premise;
- scan ambient facts after an exact indexed lookup failed;
- use suffix order or membership as provenance;
- switch to a broad arithmetic or inconsistency prover after a selected rule
  failed to carry its premise; or
- silently fall back from a proof-object descendant to a parallel checking
  path.

The current tree contains active migration seams named or described as legacy
in claim certification, pure theorem checking, resource fact adapters, loop
planning, explicit linear checking, proof drains, and surface synthesis. This
issue requires an inventory of those paths and deletion of every legacy path
that can provide semantic authority. Do not merely rename them.

Not every algorithmic alternative is forbidden. A bounded search tactic may
try several explicitly documented strategies, and a read-only query may use a
sound indexed secondary representation. Such alternatives must have the same
checked semantics, explicit budgets, deterministic selection, and no authority
to reconstruct missing proof evidence. They should be named for their rule or
index, not “legacy fallback.”

During migration, an incomplete new path must fail promptly and visibly. It
must not silently route ordinary verification through the old engine. Tests
that count fallback use should be converted into tests that assert the old
path is unreachable, then the counter and path should be deleted.

### Expunge, do not bypass

Completion requires physically deleting the old semantic-recovery machinery.
It is not enough to make a new path preferred, leave the old path behind an
`else`, retain it for “difficult cases,” mark it dead, or keep a counter that
normally reads zero. Dormant proof-authority code continues to expand the
trusted and reviewable surface, invites future callers, and lets later changes
silently revive the old semantics.

Before implementation begins, check in a concrete inventory of every active
legacy certifier, compatibility adapter, reconstructed semantic fact/state
view, semantic re-lowering route, and fallback counter in the affected proof
pipeline. Each migration chunk must delete inventory entries together with
their code and tests. The final gate is an empty inventory plus source-scope
regressions that reject new proof-authority APIs using those patterns. Any
intentional remaining reconstruction must be presentation-only, must recheck
against an exact retained identity, and must be documented by narrow purpose;
it cannot establish semantic authority.

## Intended regressions

First reduce the stashed arena failure to one small unchanged C function and
sidecar. The positive composition must include only the features needed to
reproduce the identity loss:

- a named composite resource with a uniquely selected conditional arm;
- two declaration-order facts, where the second depends on the first and
  quantifies over contained memory;
- a proof match or unfold that exposes the selected arm and its payload;
- a loop invariant that restates one exposed fact at loop entry;
- explicit instantiation of the quantified fact at a symbolic index; and
- an obvious one-premise arithmetic consequence in a mid-execution `have`.

Write the proof using the natural explicit operations. Do not qualify it with
irrelevant snapshots, duplicate facts, expose implementation-only load names,
or add tactics whose only purpose is steering the prover around stale
selection. Verification, profiling, expansion, verification of the expansion,
and audit must all accept the same proof.

Add focused tests alongside that composition regression:

- two facts with identical Surface Click spelling but distinct snapshot or
  binder identity; citing one must select only the explicitly paired checked
  fact, and an unscoped ambiguous citation must fail;
- a single checked fact with two authorized presentations; both must resolve
  to the same retained identity without re-lowering it as new evidence;
- a smart atomic derivation whose selected exact premises survive
  serialization and independent checking;
- tampering with a serialized premise identity, binder, snapshot, or polarity
  must be rejected;
- direct one-premise arithmetic with 8, 16, 32, and 64 unrelated facts must
  show output-sized work rather than an ambient scan;
- mid-execution `have` at increasing unrelated path lengths must have a
  deterministic scaling regression and enforced budget; and
- profiling and expansion of the composition regression must pass the
  small-stack canary.

The large arena proof remains a final integration regression after these small
tests are green. It is not the development loop for the architectural fix.

## Required design direction

Do not prescribe a public syntax change before the reduction is complete, but
the fix must establish these properties:

1. Kernel operations return typed, ordered proof deltas that retain exact fact
   and derivation identity, including selected conditional path, binders,
   snapshot, and source-clause correspondence where applicable.
2. The proof object owns those deltas through nested scopes, loop heads,
   resource rewrites, instantiation, and claim completion.
3. Surface presentation records a scoped relation to an exact retained fact.
   Lookup starts from that fact identity; it never chooses semantic authority
   from unqualified source text.
4. Smart tactics build only from checked operations and return the exact
   retained certificate/provenance DAG for their successful descendant.
5. Expansion serializes that DAG. Independent checking consumes it. Neither
   phase re-runs smart search, reconstructs state, or consults a legacy proof
   engine.
6. Current-state or snapshot presentation changes are explicit checked
   transports with narrow rules and retained evidence.
7. Simple rules receive their selected inputs directly and use indexed exact
   queries. Their complexity is independent of unrelated project, path, and
   proof history.
8. All user-controlled or generated certificate traversal is iterative or
   otherwise protected by an enforced stack-depth budget with actionable
   diagnostics.

A stable internal fact handle may be part of the solution, but adding IDs
without fixing lifetime, scope, binder, snapshot, and certificate transport
would only hide the same reconstruction behind another map.

## Work sequence

1. Reduce and commit the small failing composition regression without changing
   the C pattern or proof intent. Quarantine it only while this issue remains.
2. Inventory active legacy semantic fallbacks and identify which exact evidence
   each one is compensating for.
3. Specify the producer/consumer proof-delta contract and the permitted
   presentation relationship in `docs/internals/proof-objects.md`.
4. Migrate one complete vertical path—from checked rule, through proof object,
   smart construction, serialization, expansion, and independent checking—so
   it has no fallback.
5. Migrate the remaining affected resource, loop, instantiation, `have`, and
   claim paths; delete the superseded certifiers, adapters, counters, and
   reconstruction code as each path becomes complete.
6. Add the identity, tampering, scaling, and stack regressions.
7. Return to the stashed natural arena proof only after the reduced regression
   and all proof-tool gates are green.

## Acceptance criteria

- The reduced natural proof verifies without proof-only C changes, irrelevant
  bookkeeping, implementation load names, or inflated budgets.
- `click verify`, `click profile`, `click expand`, verification of expanded
  output, and `click audit` agree on the regression.
- A smart tactic cannot report success unless its exact checked descendant is
  serializable and independently verifiable.
- Exact facts survive resource match/unfold/fold, loop invariant entry,
  quantifier instantiation, mid-execution `have`, and claim certification
  without source-text selection or fresh semantic lowering.
- Ambiguous equal-looking historical facts are never selected by spelling or
  ambient order.
- All active legacy proof-authority fallbacks in the affected paths are
  expunged from the source. No ordinary verification path can enter a legacy
  certifier, reconstructed fact vector, repeated-execution engine, or semantic
  re-lowering path, and no dormant compatibility version remains callable.
- Direct simple rules and mid-execution `have` satisfy deterministic scaling
  regressions over multiple sizes, with work proportional to explicit inputs
  and produced proof delta up to logarithmic indexing factors.
- Profiling, expansion, and checking remain within the small-stack budget and
  fail promptly with bounded diagnostics when a budget is exceeded.
- The parameterized adjacent arena allocation verifies with its original
  natural proof strategy, and the remaining arena ownership work can resume.
- `scripts/check.sh` passes.
