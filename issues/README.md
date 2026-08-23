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

- [Retire the parallel replay proof engine](replay-smell.md): ordinary source
  verification and expansion still advance a large mutable semantic state in
  parallel with the checked `Proof` model.
- [Resource tracking across execution transitions](resource-tracking.md):
  owned-vector retains persistent `observe` projections across a consuming
  reallocation; audit the existing scoped resource mechanism and ensure
  direct and opaque frontier steps apply one documented lifetime law.
- [Owned-vector provisional ensure scaling](owned-vector-provisional-ensure-scaling.md):
  after the resource transition advances, dynamic range membership repeatedly
  scans the proof context while lowering a later verified call's ensures.
