# Open issues

`master` is expected to pass the default test suite. Known-broken or
pathologically slow cases are skipped by the explicit quarantine lists in
`tests/mdtests.rs` and `tests/examples.rs`.

## Tactic vocabulary cleanup

The tactic naming work is split into three ordered, independently reviewable
changes:

1. [Canonicalize the tactic vocabulary](tactic-vocabulary-cleanup.md).
2. [Unify the execution tactics](tactic-execution-unification.md).
3. [Remove tactic spelling and semantic traps](tactic-semantic-consistency.md).

The first issue records the common naming policy and the mechanical portion of
the migration. The later issues make the larger behavioral changes. Each issue
includes its own tests and documentation work so it can be understood and
completed without relying on conversation history.
