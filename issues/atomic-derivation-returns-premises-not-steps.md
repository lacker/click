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
