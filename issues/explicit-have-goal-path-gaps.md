# Explicit have scripts cannot move onto the goal path yet

## Violated invariant

The drain's goal-based smart-`have` path should carry every `have` the
legacy checker carries. A sound (`--nocapture`) probe over the fixture
gates shows the goal path misses 1023 times per full run, and 77% of the
misses are fully explicit single-tactic scripts (`[Normalize]` 312,
`[Assumption]` 145 in mdtests alone) that `try_linear_smart_script`
declines *by design* — searchless scripts belong to explicit certificate
checking, and the drain site lacks the `check_certificate` branch the
scope drivers already have.

Adding that branch (attempted 2026-08-18, reverted) exposed two blockers
in `mdtests/field_derived_precise_effect_after_metadata_write.md`
(`buffer_push.contract`, statement 6, source tactic 6):

1. **Strictness policy**: three explicit have certificates there carry
   tactics after a goal-closing step. The legacy checker tolerates the
   redundant suffix; the strict `Proof` path rejects ("a tactic follows a
   goal-closing step"). Either the goal path gains bounded
   suffix-tolerance (mirroring its final-`simp` no-op rule) or the
   fixtures' scripts are cleaned — a policy decision, since the scripts
   are proof code, not C.
2. **Checker performance**: one of the explicit certificates consumes the
   entire 2,000,000-unit deterministic control budget inside
   `ProofScope::check_certificate` where the legacy
   `checked_have_with_proof` is cheap. Checking the same certificate
   through the strict scope path must not cost orders of magnitude more;
   this is a scalable-verification violation to reduce and fix before the
   dispatch lands.

## Reduction (2026-08-18, second pass)

The budget sink is isolated to one certificate shape in the reproducing
mdtest: a nested `[Have, TransportUsing, Assumption]` explicit body takes
19.2 seconds through `ProofScope::check_certificate` (its sibling of the
same shape takes 3 milliseconds), exhausting the 2,000,000-unit budget
inside the check. Timing attribution puts 1.34M units / 8.8s in kernel
"general alias: range" under "resource context equality" — per-candidate
alias queries during the nested transport's matching. Both paths end in
the same checker (`check_point_fact_transport_using_facts`); the
difference is the operation view: the goal path's `PointOperationView`
supplies replay-derived effect facts where the legacy point root supplies
the path's transition facts, and the byte-granular memory context of this
test makes the larger effect set explode the alias search. Next step:
compare the two views' input sizes at the slow have and bound or index
the transport's candidate enumeration (exact-first, alias-bounded), per
the complexity contract.

## Intended regression

- A deterministic curve comparing goal-path versus legacy explicit-have
  certificate checking on the reproducing certificate shape (metadata
  write / field-derived effect context), pinning near-parity cost.
- The dispatch change itself (searchless scripts route to
  `scope.check_certificate`), landing only when the mdtest passes with no
  budget increase, plus a probe assertion that the have-miss count drops
  by the explicit-script share.

## Acceptance criteria

- `MDTEST_FILTER=field_derived_precise_effect_after_metadata_write` green
  with the dispatch in place and unchanged budgets.
- The suffix-tolerance decision is recorded in the proof-object API doc,
  and whichever side is chosen has a regression.
- The sound-probe have-miss count over the gates drops accordingly; the
  remaining misses are genuinely searching scripts.
