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
- [Replace pairwise resource-context work with indexed algebra](indexed-resource-algebra-avoids-pairwise-context-work.md):
  the last eager pair emission is deleted on a prototype branch; one test
  remains, its diverging query is traced to call-havoc load framing, and
  the decided design (stratified derivation edges plus canonical terms
  with bounded guards) is recorded in the issue.
- [Canonical load jump launders havoc markers](canonical-load-jump-launders-havoc-markers.md):
  a kernel soundness gap — the materialization-source jump in load
  canonicalization erases havoc markers, so a load can be treated as
  unchanged across a havoc of its own pointer; the one-hunk fix exposes a
  premise-bridge completeness debt in input-cursor shared with the
  lazy-separation close-out.
- [Declared resources need symbolic quantities](symbolic-declared-resource-quantities.md):
  every `owns`/`consumes`/`produces` clause transfers exactly one unit, so
  runtime-sized capacity cannot become linear authority; bounded-pool is the
  motivating case.
