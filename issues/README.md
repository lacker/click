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

## Other open issues: 6

- [Two sorts of canonicalization](two-sorts-of-canonicalization.md):
  memory-provenance normalization and proof-context equality normalization
  can produce competing forms, leaving consumers to compose them in an
  order-dependent way instead of receiving one producer-side normal form.

- [Canonical pointer offsets need a production invariant](canonical-pointer-offset-invariant.md):
  loaded pointer values are canonicalized today, but no regression walks
  production-generated pointers and rejects a nested `MemoryLoad` in their
  offset arithmetic.
- [Canonical loaded offsets need a scaling curve](canonical-loaded-offset-scaling.md):
  the motivating metadata-write proof is green, but its deterministic work
  is not pinned over multiple input sizes.
- [Expansion replay recursion exhausts the stack](expansion-replay-recursion-exhausts-the-stack.md):
  ordinary edits — a local, a closure, an unboxed enum payload — abort an
  unrelated expansion test with a stack overflow and no backtrace; the
  depth is unbounded and unmeasured, and `#[inline(never)]` adapters are
  holding it back.
- [Fixture gates decide green from wall clock](fixture-gates-decide-green-from-wall-clock.md):
  the mdtest and example harnesses enforce real-time limits, so machine
  load flips `scripts/check.sh`'s verdict on an unchanged tree; the
  verifier already has load-independent unit budgets to decide with.
- [Observed views survive reallocation](observed-views-survive-reallocation.md):
  owned-vector now fails promptly because child views observed from an owned
  allocation remain usable after `vector_grow` retires that allocation.
