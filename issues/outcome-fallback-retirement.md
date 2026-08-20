# Delete outcome compatibility and legacy exit infrastructure

## Violated invariant

The proof-object migration is not complete while ordinary verification can
construct a second certificate from semantic aftermath or route a function
outcome through the legacy exit planner. Even if every current passing fixture
chooses the direct path, retaining live fallbacks makes future tactic families
silently regress to the old architecture.

This is the terminal migration leaf. It depends on the other eight open
leaves; it must delete infrastructure rather than add a zero-corpus guard
around dead code.

## Deletion inventory

Reconfirm names at implementation time. The current inventory includes:

- `lower_outcome_simp_proof` and outcome compatibility construction;
- `certify_outcome_simp_have`, grouped outcome-simp transition builders, and
  per-claim legacy exit closure paths;
- `with_drained_outcome`, `available_fact_vector`, working-set dirty resyncs,
  and other adapters whose only callers bridge typed outcomes back to vectors;
- obsolete planner/evidence records and timing spans used only by those paths;
  and
- issue-journal comments that describe already-deleted compatibility behavior.

Do not delete general explicit-certificate checking: source proofs, `click
expand`, and `click audit` must continue to check separately supplied
certificates.

## Intended regression

- A repository-wide source census proves the deleted functions, types, spans,
  and adapter names have no live definitions or call sites.
- Instrumented mdtest and example gates report zero compatibility and legacy
  exit events for both passing and expected-failure fixtures.
- Representative expansion and audit tests cover pure, quantified, branch,
  resource, call/effect, and negative diagnostic classes.

## Acceptance criteria

- Ordinary verification has no semantic path that reconstructs or ordinarily
  replays a successful smart tactic after its checked `Proof` transition.
- All obsolete compatibility/legacy outcome code is deleted, not merely
  unreachable on the current corpus.
- The architectural acceptance criteria in `issues/proof-object-api.md` are
  audited requirement by requirement against current code and tests.
- `scripts/check.sh` passes, the fallback census is zero, and expansion/audit
  independently verify the retained certificates.
