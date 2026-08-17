# Atomic derivation returns premises, not steps

Smart proposition search ends in `SimpEvidence::Derivation(PropositionDerivation)`,
which records the conclusion and the premise facts but not how the prover
combined them. The prover decided through concrete theory rules — an order
path, an equality chain, an interval bound, a normalization — and discarded
that structure at the interface. Certificate construction must then
rediscover it: `lower_surface_atomic_derivation` guesses the rule through the
named-rule cascade, re-establishes premise minimality by deletion with a full
replay validation per candidate, and harvests rewrite candidates from the
ambient context. Construction is a second search compensating for a lossy
type.

The cost is measured, not inferred. The budget-exhaustion attribution spans
show `box_pipeline`'s three-step `have` spending about 22,000 units finding
its proof and 979,000 spelling it — 97 percent of construction inside the
ambient rewrite harvest, which spelled every ambient equality through
snapshot-aware search before knowing whether the planner needed any of them.
Reordering construction to try the planner's own premise pairs first (landed
with this issue) collapsed that tactic from over 2,000,000 units to under
100,000 and roughly halved the whole unit-test suite's wall time. That
reorder is relief, not the fix: the harvest, the deletion loop, and the
cascade still run whenever the premise pairs alone cannot spell the proof,
and each remains an ambient-context search inside what the complexity
contract requires to be certificate-proportional work.

## Required design

`PropositionDerivation` (or a successor type) carries typed proof steps
recorded by the theory rule that fired, at the moment it decides:

- an order-path decision records the traversed edge chain as applications of
  the named transitivity/bound theorems it already corresponds to;
- an equality-chain decision records the rewrite list in order;
- an interval/overflow decision records the named bound theorem and its
  operand facts;
- a normalization decision records `normalize`.

Certificate construction consumes the steps: spell each step's premises
(work proportional to the step list), emit the corresponding surface tactics,
and validate once. No named-rule guessing, no deletion re-minimization, no
ambient harvest. The named simple rules to express each decision largely
exist from the `simp() using` migration; what is missing is the prover
filling them in as it decides. This is the certificate-layer completion of
the closed context-wide-derivation issue, whose required design said
"certificate construction should consume this provenance rather than
rediscover a small premise set through deletion" — a criterion previously
verified only at the kernel layer.

## Where the code lives

- `SimpEvidence` and `plan_simp_certificate`: `src/lang/click/checking/simp.rs`.
- The lossy consumer: `lower_surface_atomic_derivation` in
  `src/lang/click/proof/surface_certificates.rs` — premise spelling, the
  deletion-minimization loop, the ambient rewrite harvest, and the named-rule
  cascade are all in its body, each under a `derivation lowering:` span.
- The landed relief ordering sits immediately before the harvest in the same
  function.
- To measure: run the failing shape under `CLICK_TIMINGS=1` with a lowered
  smart budget in `TacticWorkLimits::default()` (`src/instrumentation.rs`);
  the budget-exhaustion message prints the open-span stack and top completed
  spans.

## Regression design

Hold one fixed derivation of each kind — a two-premise order chain, an
equality rewrite chain through one intermediate, an increment bound, and a
snapshot-crossing store equality — while growing unrelated ambient facts of
every other kind. Measure certificate construction work through the existing
`derivation lowering:` spans. Construction must be near-constant in ambient
context size; today the harvest alone makes it linear-times-spelling-cost.

The `box_pipeline` modular-call test is the integration pin: its `have`
must stay under 100,000 smart units. The budget-exhaustion attribution
message is the diagnostic of record for any regression.

## Acceptance criteria

- Theory decisions in the atomic prover record their steps as they fire;
  no decision path returns a bare premise list.
- `lower_surface_atomic_derivation` contains no deletion-minimization loop
  and no ambient equality harvest; the named-rule cascade survives only as
  a translation table from recorded steps to surface tactics.
- Fixed-derivation construction curves are near-constant in unrelated
  ambient facts.
- Expansion output on the existing corpus changes only where certificates
  become smaller or premise lists shorter, and every changed certificate
  still replays and audits.
- The relief ordering (premise pairs before harvest) becomes dead code and
  is removed with the harvest.

## New reproduction (2026-08-14, lazy-separation prototype)

`mdtests/field_derived_precise_effect_after_metadata_write.md` is
quarantined against this issue. `buffer_push_preserves_first`'s smart
`frame()` finds its plan, but lowering the contextual frame certificate
re-searches for surface premises and fails twice over: an
execution-certified `addition overflow is false` fact has no Surface
Click spelling (widening the atomic check with ambient overflow facts
landed but is not sufficient alone), and a recovered spelling references
the C local `ignored` after it leaves scope (unlowerable pairs are now
dropped rather than fatal, which advances the failure to a missing
int32-equality premise). Every layer of this dance exists only because
the derivation records premises instead of typed steps; with steps, the
certificate transcribes instead of re-searching. The progress note below
records the narrower provenance fix that de-quarantined this reproduction
while leaving the general typed-step work open.

### Progress (2026-08-15)

The `addition overflow is false` premise already has the public spelling
`defined(owner->len + 1)`. The certificate path now retains that exact
parameter-only recorded spelling, explicit `step() using` replay accepts the
still-available certified fact instead of re-evaluating it against a folded
later heap, and direct snapshot transports preserve its surface name during
both planning and explicit replay. The focused
`defined_expression_snapshot_transport.md` regression pins this behavior.

That advances the reproduction past the unexpressed premise. It now fails
with every selected premise spelled but the flat premise set unable to replay
the pointer-offset equality. The equality was decided by following the
kernel's embedded memory-derivation DAG across snapshots; conservative
context collection includes several transported identity facts whose reused
surface spellings lower to reflexive truth rather than the distinct DAG edges
the decision traversed. Closing this issue therefore still requires a typed
memory-derivation-path step (along with the order/equality/overflow steps
above), rather than more ambient premise recovery.

The quarantined reproduction was fixed on 2026-08-15 without weakening this
broader issue. Opaque-call footprint evaluation now retains theorem-backed
transport of relevant source requirements, threads those facts across the
complete footprint, and exposes the selected transport to effect-certificate
planning. The frame can therefore use the caller's explicit
`owner->data == data` dependency instead of selecting the stronger anonymous
memory-DAG proof. The mdtest is no longer quarantined, but the general
typed-step and deterministic-scaling acceptance criteria above remain open.

### Progress (2026-08-16: signed-order paths)

Exact signed-order decisions now retain the ordered edge path selected by the
kernel. Replay checks each recorded `<`/`<=` edge directly against the exact
fact index and verifies the accumulated strictness; it does not ask the order
solver to rediscover another path. Certificate lowering matches those edges
to their Surface Click spellings in recorded order, skips deletion
minimization and full-context recovery for a complete spelling, and
transcribes paths of arbitrary length into nested `have` facts using the
four named transitivity theorems. A three-edge mixed strict/non-strict
regression expands and independently reverifies that transcription, and the
existing unrelated-condition scaling curve remains green.

This closes the exact signed-order member of the required design, not the
issue. Interval/overflow decisions, quantified/derived order edges,
memory-canonicalized and pointer-offset-derived equality edges, and memory-DAG
joins still return legacy or incomplete evidence and must gain their
corresponding typed steps before the ambient harvest and deletion machinery
can be removed globally.

The pure smart-tactic consumer now also uses this provenance at the Proof
boundary. Its requirement spellings live in the existing persistent
kernel/surface index; the selected path becomes a candidate made from named
`ApplyTheoremUsing` steps and nested `Have` scopes, and those operations build
the accepted immutable `Proof` directly. Ordinary verification of the
three-edge chain therefore emits no `surface certificate replay`; expansion
still independently verifies the serialized certificate. The point/outcome
consumer still lowers typed paths through its certificate planner and remains
migration work under the proof-object issue.
A deterministic 16-through-4096 unrelated-fact regression pins logarithmic
persistent updates for the same retained theorem path; the order search itself
remains the separately measured near-linear smart-planning phase.

### Progress (2026-08-16: exact int32 equality paths)

The existing lazily shared equality graph now retains one exact source
proposition on each edge. Exact ground-int32 equality decisions record the
oriented path they traverse; replay checks every source condition by indexed
lookup and follows the recorded endpoints without rerunning graph search.
Memory-canonicalized vertices and pointer-offset-derived edges are excluded
from this evidence kind until their distinct proof rules are typed.

Pure certificate selection orients each recorded source spelling, emits the
ordered `rewrite` steps, and finishes the resulting reflexive goal with
`normalize`. The smart tactic submits that candidate to the immutable `Proof`
and retains the accepted descendant, so ordinary verification emits no
`surface certificate replay`; expansion independently reparses and verifies a
three-edge path, including a source equality written in reverse. The existing
equality-index regression confirms many graph queries still share one ambient
fact-index build.

### Progress (2026-08-16: point and outcome consumers)

Point and post-execution outcome `simp` now consume exact signed-order and
ground-int32 equality paths through the immutable `Proof` rather than asking
the legacy certificate planner to rediscover a derivation. The existing exact
Surface proposition index supplies only the recorded edge spellings. Signed
paths submit the selected named theorem applications, nested `have` scopes,
and their joins to `Proof`; equality paths submit the selected oriented
rewrites and `normalize`. The accepted descendant is the certificate.

The point theorem transition closes an exact matching goal immediately,
unlike the pure transition which adds a conclusion for a subsequent
`assumption`; the recorded-order planner now represents that distinction
explicitly and never emits a redundant point closer. Result-dependent outcome
regressions expand and independently verify both path kinds, and deterministic
16-through-4096 unrelated-fact curves cover the point theorem and equality
paths. The legacy atomic lowering path also recognizes a fully spelled typed
equality path before deletion minimization and ambient equality harvesting.

This does not close the issue. Interval/overflow decisions,
quantified/derived order edges, memory-canonicalized and pointer-offset-derived
equality edges, memory-DAG joins, and execution-frontier consumers still need
typed evidence and direct Proof operations.

### Progress (2026-08-16: first typed arithmetic rules)

The atomic int32 increment-upper-bound, increment-strictly-increases,
increment-below-max-definedness, and increment-lower-bound decisions now
record typed evidence when a rule fires. The first three retain one exact
strict source edge. Increment-lower-bound retains both its exact non-strict
lower edge and strict upper edge. None is inferred later from a minimized
premise bag: replay checks every retained edge orientation, strictness, exact
source proposition, increment shape, and rule-specific goal operand
directly. Reversed `upper > value`, `INT32_MAX > value`, and
`value >= lower` source regressions pin that the original premises survive.

Standalone pure `simp() using` now has a restricted Proof query shared by all
currently typed atomic paths: it lowers only the explicitly listed premises,
searches only that small fact context, and submits the resulting typed
order/equality/arithmetic candidate to the original immutable `Proof`.
Point/outcome `simp` consumes the new increment evidence through the same
theorem-application seam. Ordinary verification no longer constructs and
independently replays these certificates, while expansion still emits and
independently verifies `int32_increment_upper_bound`,
`int32_increment_strictly_increases`,
`int32_increment_below_max_is_defined`, and exact equality paths.
The same path independently verifies the two-premise
`int32_increment_lower_bound` application.
Deterministic 16-through-4096 unrelated-fact curves cover both unrestricted
point search and restricted pure search, including rejected-premise
transactionality.

The remaining two-premise increment-bound family now uses the same seam.
`int32_increment_greater_equal_lower_bound`,
`int32_increment_strict_greater_lower_bound`, and
`int32_increment_preserves_order` each retain a distinct typed rule variant
containing the exact lower and strict-upper source edges. Their replay checks
the rule-specific conclusion shape and both original facts by exact index
lookup. Point/outcome and restricted pure `simp` submit the corresponding
named theorem application to `Proof`; ordinary verification does not enter
surface-certificate replay or ambient rewrite harvesting. The shared
16-through-4096 family curve covers accepted applications, either-premise
rejection, ancestor isolation, and logarithmic persistent allocation.

The three direct predecessor rules now retain typed evidence as well.
`int32_positive_predecessor_is_nonnegative` and
`int32_positive_predecessor_strictly_decreases` retain the exact strict
positivity source. `int32_nonnegative_predecessor_upper_bound` retains its
exact nonnegative and upper-bound sources behind a boxed two-edge payload.
Exact direct-edge selection probes the four polarity/orientation spellings by
persistent-map lookup, so a coexisting strict and non-strict edge cannot make
the path chooser discard the theorem's required source. Replay checks the
literal predecessor shape, rule-specific conclusion, endpoints, strictness,
and exact original facts. Point and restricted-pure Proof regressions cover
all three rules over 16 through 4096 unrelated facts, including rejected
premise subsets; independent expansion checks all three named applications.

Outcome predecessor proofs that first derive a missing nonnegative leg by
equality rewriting deliberately remain legacy. Their retained object must
include that nested equality derivation rather than falsely presenting the
derived leg as a direct source premise.

The first derived predecessor decisions now retain that nested structure.
Given an exact `1 <= value` source, the kernel records the selected source
edge for both `0 <= value - 1` and `value - 1 < value`. Certificate planning
first derives `0 < value` with `int32_successor_le_implies_lt(0, value)` in a
scoped `have`, then applies the corresponding direct predecessor theorem.
Both theorem applications advance the immutable `Proof` when selected; there
is no later premise minimization or rediscovery of the intermediate fact.
Replay validates the literal predecessor shape, exact source orientation,
endpoints, and non-strictness before accepting either evidence variant.

This slice also pins a structural distinction that reconstruction previously
obscured: an exact point theorem application closes its goal immediately,
including a goal nested inside `have`, while the pure proof retains an
explicit following `assumption`. Point and pure expansion regressions require
the corresponding certificate shapes and independently reverify them.
Rejected source omission is transactional, and the shared 16-through-4096
unrelated-fact curve keeps the retained two-application derivation within the
logarithmic persistent-update bound.

The two signed equality rules now retain their exact source-supported theorem
orientation. `left <= right` plus `not (left < right)` records
`int32_le_and_not_lt_implies_eq`; the dual `left >= right` plus
`not (left > right)` records `int32_ge_and_not_gt_implies_eq`. Selection and
replay use exact indexed fact membership, not a derived equivalent order fact,
so neither rule can be reconstructed from anonymous solver aftermath. Pure,
point, and outcome smart `simp` submit the selected application directly to
the immutable `Proof`; fixed-size polarity probes recover Surface spellings
without an ambient scan. Deterministic 16-through-4096 coverage pins the
persistent-update bound, and expansion independently verifies both named
applications.

The direct positive-to-nonnegative decisions now retain their exact edges:
`1 <= value` as `int32_positive_is_nonnegative` evidence and `0 < value` as
`int32_strictly_positive_is_nonnegative` evidence. Restricted pure and
point/outcome smart `simp` consume that evidence through the existing
theorem-application seam, with no ambient premise search or construction
replay. The shared 16-through-4096 single-premise curve covers accepted and
omitted-premise behavior, and expansion independently verifies both named
applications.

Multi-premise evidence is stored behind an indirection. Inlining the two
retained propositions in the evidence enum enlarged unrelated recursive proof
frames enough to overflow the existing deeply branched `sort3` expansion.
The focused branch regression and an evidence-size invariant now prevent new
typed rule payloads from silently increasing every checker frame.

A real post-execution `ensures defined(value + 1)` regression exposed that
contract certification possessed the exact maximum bound but intentionally
did not invoke the smart overflow solver. Certification now has the same
narrow, fuel-free one-premise rule as the named theorem; this does not admit
general interval reconstruction into the simple checker.

These are the first members of the interval/overflow family, not completion
of that family. Other arithmetic-definedness, derived predecessor, interval,
and derived-order decisions remain `Legacy` until each decision retains its
exact rule and operands.

The signed equality rule `left <= right` plus `not (left < right)` now retains
those two exact source conditions behind a boxed typed evidence value. Replay
checks the equality goal shape and both recorded condition values directly;
it does not rerun order search. Pure and point `simp` consume the evidence as
one checked `int32_le_and_not_lt_implies_eq` application through `Proof`.
The pure Surface spelling may remain structural `not (...)` while the kernel
condition index stores the equivalent false condition; selection resolves
that fixed polarity family by bounded exact-index probes rather than an
ambient scan. Expansion independently verifies the named step, omitted
premises are transactional, and the 16-through-4096 unrelated-fact curve
pins logarithmic Proof updates.
