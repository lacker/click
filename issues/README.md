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

## Open

- [Proof object API](proof-object-api.md): smart tactics need one immutable,
  cheaply forkable checked `Proof` interface where applying a
  `SimpleProofStep` atomically advances semantic state and retains the exact
  structured certificate, eliminating after-the-fact reconstruction and
  ordinary per-tactic replay.
- [Atomic derivation returns premises, not steps](atomic-derivation-returns-premises-not-steps.md):
  smart search discards how it proved its goal, so certificate construction
  re-searches; measured at 97 percent of one tactic's budget before the
  landed relief ordering.
- [Push contract path dropped by laundered inconsistency](push-contract-path-dropped-by-laundered-inconsistency.md):
  the silent sibling-path drop now has a structural guard; honest
  `allocated_vector_push.contract` verification still stalls in giant-term
  verified-call ensure lowering during independent kernel certification, so
  owned-vector remains quarantined. A generated-step deadline was separately
  isolated as outer smart expansion-validation attribution, not a slow simple
  checker.
