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

- [Canonical load names do not connect across effects](canonical-name-transport-across-effects.md):
  explicit transports cannot connect recorded-point and current-point
  canonical names across call havocs or undecided-alias stores; blocks
  the last two check.sh failures on the canonicalization branch, with
  the design options and both reproductions characterized.
- [Load terms in arithmetic positions](load-terms-in-arithmetic-positions.md):
  unresolved memory loads inside pointer offsets make alias queries
  recursive (8 queries fan out to 1.6M units); the shared root cause
  behind the explicit-have budget gap and the owned-vector quarantine,
  with a scoped canonicalization design.
- [Explicit have scripts cannot move onto the goal path yet](explicit-have-goal-path-gaps.md):
  searchless source scripts and ground universal instantiation now check
  directly inside the typed outcome goal; the file also carries the remaining
  outcome-`simp` planner and legacy-exit-closer migration journal, whose
  binder-aware quantified, rewrite, and loadability residues still fall back.
- [Expansion replay recursion exhausts the stack](expansion-replay-recursion-exhausts-the-stack.md):
  ordinary edits — a local, a closure, an unboxed enum payload — abort an
  unrelated expansion test with a stack overflow and no backtrace; the
  depth is unbounded and unmeasured, and `#[inline(never)]` adapters are
  holding it back.
- [Fixture gates decide green from wall clock](fixture-gates-decide-green-from-wall-clock.md):
  the mdtest and example harnesses enforce real-time limits, so machine
  load flips `scripts/check.sh`'s verdict on an unchanged tree; the
  verifier already has load-independent unit budgets to decide with.
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
