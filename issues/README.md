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

- [Atomic derivation returns premises, not steps](atomic-derivation-returns-premises-not-steps.md):
  smart search discards how it proved its goal, so certificate construction
  re-searches; measured at 97 percent of one tactic's budget before the
  landed relief ordering.
- [Push contract path dropped by laundered inconsistency](push-contract-path-dropped-by-laundered-inconsistency.md):
  the exit drain's "sibling certifies this path" skip silently dropped the
  `grown == 1` path of `allocated_vector_push.contract` on master, hidden
  by launder-induced inconsistency; honest re-verification lands on this
  branch and stalls only on giant-term memory-resolution cost, with
  owned-vector quarantined until the engine work and a no-silent-drop
  guard land.
