# A ledger with an active hold is equal to its hold-free predecessor

P1. Two states the kernel treats as equal must agree on every property
consulted downstream; a hold changes consulted properties while keeping the
identity.

## What was found

`LoanLedger::hold` (`src/kernel/loans.rs:3298`) inserts the hold into the
ledger *data* and returns `state: self.storage.state` — the
**predecessor's** `LoanLedgerStateId`. `LoanLedger`'s equality is pure
state-identity equality (`loans.rs:600`), deliberately documented ("A hold
keeps the ledger identity", `loans.rs:63-67`). Machine-confirmed
(`hunt_investigation_hold_does_not_change_the_ledger_identity`,
`src/kernel/loans.rs` investigation module): a ledger with an active hold
is `==` to its hold-free clone.

Consumers that trust ledger equality as "same loan state":
- `abstract_c_state_for_join_*` (`src/kernel/api.rs:933-953`): a branch join
  is accepted when the arms' ledger identities agree — two arms with
  equal-by-identity but hold-differing ledgers pass the join gate;
- `CheckedLoanCallEvidenceSummary` / `recheck`
  (`src/kernel/loans.rs:1510-1864`, the successor equality at 1815/1835) —
  evidence replay cannot distinguish hold-differing endpoints, and
  `recovered_by_caller` indexing (`1493-1536`) keys by
  `(state_identity, participant)`, so a hold set can leak across
  same-identity histories.

The backstop is only the *local* re-check inside the next transition
(`apply_evidence` refuses `End` with `holds` non-empty, `loans.rs:4593`) —
drift survives until an `End`/`Recover` arrives and nothing binds the hold
set to the identity itself.

## Intended regression

The investigation test converted to a true regression: either `hold`
mints a successor state id (hold set stamped into identity), or every
consumer of ledger equality refuses hold-differing data at the deciding
gate (`apply_evidence`), with both learners asserted: no consumer may
trust plain state-id equality to imply "same hold set".

## Acceptance

- [ ] Ledger equality cannot equate hold-differing ledgers at a deciding
      gate, with the equal-hold divergence regression refusing.
- [ ] `scripts/check.sh` green.
