# `--time-limit` does not stop a deadlocked run

Soundness: not soundness. A run that should be stopped keeps running; no
verdict changes.

`--time-limit` is documented as crash containment for "a genuinely hung or
CPU-starved run" (`CRASH_CONTAINMENT_TIME_LIMIT`, `src/cli.rs`). It is a
deadline the verifier polls (`instrumentation::deadline_exceeded`), and
`click verify` runs on one thread, so a run that stops polling is never
stopped. A deadlock is such a run.

Reproduced on master `b94efb36`, before the equality-graph fix in the same
change as this file: replacing the proof of the `have` at
`examples/arena/arena_cells.click:3118` with `by auto;` made
`click verify --time-limit 30s arena_cells.click:3118:17` block forever on a
futex with one thread (`EqualityGraph::logical_read_generation`, reached
while `EqualityGraph::are_int32_equal` held the same lock). An outer
`timeout 120` killed it; `--time-limit` never fired. In the `auto` eval the
same run sat for several hours with `--time-limit 5m`.

That deadlock is fixed, and its regression is
`tests/examples.rs::auto_on_an_arena_cell_read_answers_instead_of_deadlocking`,
but the containment gap remains: any future deadlock or loop that does not
poll will hang a run, an eval, or the gate.

Acceptance: a run that makes no progress past `--time-limit` is stopped and
reports containment, whether or not the verifier polls, for example by a
watchdog thread that ends the process. A test hook that blocks the verifier
thread (debug builds only) shows `click verify --time-limit 1s` exiting
promptly with the containment message. Ordinary runs, whose verdicts the
deterministic work budgets decide, are unaffected.
