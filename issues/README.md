# Open issues

One `.md` file per independent open problem. Each issue contains a small
intended regression, the violated invariant, and acceptance criteria. Delete
an issue when its fix, regression coverage, and documentation land. Do not
leave the only reproduction in an uncommitted example, and do not quarantine
a regression (in `tests/mdtests.rs` or `tests/examples.rs`) without a
corresponding issue here.

Policy lives in the docs, not here: `AGENTS.md` for when tooling failures
block feature work and what always warrants an issue, the
[proof-failure triage guide](../docs/advanced/proof-failure-triage.md) for
classifying a failure before filing (including the smart-versus-simple
tactic rule), [Testing Click](../docs/advanced/testing-click.md) for
quarantine, profiling order, and the expansion workflow, and
[Verification Efficiency](../docs/advanced/verification-efficiency.md) for
the complexity contract and scaling-regression policy. Proposals without a
failing deterministic curve are not open roadmap items; file a narrow issue
when evidence exposes one.

## Proof-object migration: 10 open

This is the countable endgame board. Each link is one independently closable
unit; [Proof object API](proof-object-api.md) is the architectural design and
history, not an eleventh open item. The terminal retirement issue depends on
the other nine.

- [Preserve predicate-unfold provenance through outcome goals](outcome-predicate-unfold-provenance.md):
  keep the checked unfold-owned universal index through drain resync and pair
  active predicate haves with their structural Surface bodies.
- [Close bound universal outcomes with explicit specialization and transport](outcome-bound-universal-transport.md):
  remove the last two passing legacy-exit sites by retaining binder-aware
  instantiate/transport certificates.
- [Atomic derivation returns premises, not steps](atomic-derivation-returns-premises-not-steps.md):
  make scalar and statement/effect decisions return typed steps so outcome
  certificate construction no longer re-searches.
- [Retire outcome compatibility for snapshot and post-call transports](outcome-snapshot-call-transport-compatibility.md):
  retain the selected source/target transport across calls and snapshots.
- [Retire outcome compatibility after checked branch continuations](outcome-branch-continuation-compatibility.md):
  close joined outcome claims on the same checked branch DAG.
- [Keep resource-backed example pipelines on outcome Proof](outcome-resource-example-pipelines.md):
  remove compatibility construction from the linked-list and recursive-list
  vertical examples.
- [Preserve pure and type failure diagnostics without outcome fallbacks](outcome-negative-pure-diagnostics.md):
  keep arithmetic, type, logic, and invalid-tactic failures direct and bounded.
- [Preserve stale-memory and mutation failures without outcome fallbacks](outcome-negative-memory-diagnostics.md):
  reject invalidated snapshot/effect claims without the legacy closer.
- [Preserve resource and call failures without outcome fallbacks](outcome-negative-resource-call-diagnostics.md):
  keep missing-resource, opaque-call, and grouped-proof diagnostics on typed
  goals.
- [Delete outcome compatibility and legacy exit infrastructure](outcome-fallback-retirement.md):
  remove the adapters and planners, prove a zero-event corpus census, and run
  the final requirement-by-requirement acceptance audit.

## Other open issues: 5

- [Canonical load names do not connect across effects](canonical-name-transport-across-effects.md):
  explicit transports cannot connect recorded-point and current-point
  canonical names across call havocs or undecided-alias stores; blocks
  the last two check.sh failures on the canonicalization branch, with
  the design options and both reproductions characterized.
- [Load terms in arithmetic positions](load-terms-in-arithmetic-positions.md):
  the canonicalization fix landed; deterministic position, budget, scaling,
  and owned-vector acceptance evidence remains before closure.
- [Expansion replay recursion exhausts the stack](expansion-replay-recursion-exhausts-the-stack.md):
  ordinary edits — a local, a closure, an unboxed enum payload — abort an
  unrelated expansion test with a stack overflow and no backtrace; the
  depth is unbounded and unmeasured, and `#[inline(never)]` adapters are
  holding it back.
- [Fixture gates decide green from wall clock](fixture-gates-decide-green-from-wall-clock.md):
  the mdtest and example harnesses enforce real-time limits, so machine
  load flips `scripts/check.sh`'s verdict on an unchanged tree; the
  verifier already has load-independent unit budgets to decide with.
- [Push contract path dropped by laundered inconsistency](push-contract-path-dropped-by-laundered-inconsistency.md):
  the silent sibling-path drop now has a structural guard; honest
  `allocated_vector_push.contract` verification still stalls in giant-term
  verified-call ensure lowering during independent kernel certification, so
  owned-vector remains quarantined. A generated-step deadline was separately
  isolated as outer smart expansion-validation attribution, not a slow simple
  checker.
