# Open issues

One `.md` file per independent open problem. Each issue contains a small
intended regression, the violated invariant, and acceptance criteria. Delete
an issue when its fix, regression coverage, and documentation land. Do not
leave the only reproduction in an uncommitted example, and do not quarantine
a regression (in `tests/mdtests.rs` or `tests/examples.rs`) without a
corresponding issue here.

Policy lives in the docs, not here: `AGENTS.md` for when tooling failures
block feature work and what always warrants an issue, the
[proof-failure triage guide](../docs/concepts/proof-failure-triage.md) for
classifying a failure before filing (including the smart-versus-simple
tactic rule), [Testing Click](../docs/internals/testing.md) for
quarantine, profiling order, and the expansion workflow, and
[Verification Efficiency](../docs/internals/verification-efficiency.md) for
the complexity contract and scaling-regression policy. Proposals without a
failing deterministic curve are not open roadmap items; file a narrow issue
when evidence exposes one.

## Other open issues: 3

- [Replay is a second proof engine](replay-smell.md): independent certificate
  checking still advances a large parallel mutable replay state instead of
  interpreting recorded operations through the audited proof-object model.
- [Thread-local state leaks between verifications](thread-local-state-leaks-between-verifications.md):
  verifying `borrowed-slice` then `linked-list` on one thread fails the
  second; a thread-local memo answers across projects and a smart search
  misses its budget.
- [Resource tracking across execution transitions](resource-tracking.md):
  owned-vector retains persistent `observe` projections across a consuming
  reallocation; audit the existing scoped resource mechanism and ensure
  direct and opaque frontier steps apply one documented lifetime law.
