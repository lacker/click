# One source-tactic interpreter for every proof context

Priority: P2.

Soundness: not soundness. Every route still applies checked `Proof`
transitions, so a context that handles a tactic differently refuses a proof
or expands it differently. It does not accept a false claim. The cost is
completeness, expansion fidelity and maintainability.

P1 by user direction (2026-10-15), lowered to P2 by user direction
(2026-10-20) once the execution-frontier drivers shared one tactic function
and the post-execution closers shared one claim path. What remains is
maintainability, not a known wrong verdict.

## Done

- The linear execution continuation, a focused execution arm and a loop's
  `maintain` body apply written frontier tactics through one function,
  `apply_frontier_source_tactic`
  (`src/surface/proof/driver/execution.rs`). A written
  `transport` and `step_until` mean the same thing in each.
- What each context admits as a leaf is declared once, in
  `SourceContext` (`src/surface/proof/source_context.rs`), and
  `SourceContext::leaf_step` is the one leaf converter.
- Driver declines are typed return values (`Decline`), not thread-local
  state.
- Proof `if`, `cases` and `match` after execution are decided per outcome
  path (see "Case splits").
- After execution, claims are goals on the outcome `Proof`
  (`OutcomeClaimGoals`), and an opened claim proof is refreshed from it
  before each closer.
- The direct check in `close()` and the normalizing closers (`normalize`, `normalize using`,
  `both`) close the main claim
  through one arm of `finish_ordered_proof`, and the fallback search in `close()` and `close() using` run
  through `close_post_execution_claims_with_solve`
  (`src/surface/proof/driver/claims.rs`). `finish_ordered_proof` is about
  2,800 lines, down from 3,900.
- Expansion records the `certificate_since` delta of each checked step
  after execution. The records that keep a written spelling have no checked
  step to print:
  - a direct `close()` on a resource claim is an exact resource check;
  - a closer on a divergent path closes its claims vacuously;
  - `apply using` keeps its written spelling;
  - a `with` scope's deferred close proof is rebuilt from that close's
    checked certificate.

## Current state and violated invariant

The invariant: one function applies a written source tactic to a proof
context. A context (pure goal, execution frontier, execution arm, `with`
scope, post-execution outcome path, loop body) differs only in the `Proof`
state it supplies and in which tactics it admits, and admission is a declared
table, not a separate code path. Expansion prints what checking recorded, from
one source of truth.

These still interpret written tactics on their own:

- linear `with` scopes (`advance_linear_open_scope` in
  `src/surface/proof/driver/execution.rs`);
- explicit scripts for pure theorems, claims and smart search
  (`run_addressed_linear_script` in `src/surface/proof/driver/scripts.rs`,
  reached through `try_authoritative_linear_script`). A nested `have` that
  misses there is a decline (`LinearScriptDecline::Step` in
  `src/surface/proof/smart_closures.rs`), where the
  execution frontier reports it through `solve_nested_have`;
- loop initialization (`execution_planning/loop_planning.rs`);
- tactics after execution, through the `PostExecutionTactic` enum
  (`src/surface/proof/execution_state.rs`) and the per-path dispatch in
  `finish_ordered_proof` (`src/surface/proof/driver/claims.rs`). Its
  `Transport` variant disappears with transport retirement
  ([smart tactics](smart-tactics.md#transport-retirement), chunk 32).

`close()` in an execution arm is refused before the function exit, while a
`maintain` body has its own `close()` handler.

The largest remaining piece is the grouped closure search in
`close_post_execution_claims_with_solve`. It focuses a grouped proof's claims
together on each outcome path, closes ownership claims by exact resource
checks, falls back to each claim on its own, and keeps the bookkeeping that
lets `click expand` print the group's closers. The step that proves one
focused goal is already the shared `try_solve_closure`; the scoping around it
is post-execution only.

## Case splits

Proof `if`, `cases` and `match` follow one rule in every context
(`docs/reference/tactics/index.md`, "Case splits"). Each arm runs once.
With tactics written after the split, the live arms rejoin with the facts
every arm proved, or the split is refused. An arm that reaches function exit
is a finished path, and the closer that ends the proof closes its goals.
After execution a split that forks outcome paths does not rejoin, so tactics
after it are refused.

A `match` after execution, at function exit or nested in a post-execution
`if` or `cases` arm, is decided per outcome path through the n-way
`OutcomeEvidenceFork`. A `match` with `ensuring`, or with an arm that is a
lone `contradiction`, still splits once at the exit frontier through the
frontier `match` driver, on the facts every outcome path shares.

## Intended regression

Add mdtests that write the same tactic in each context where the language
admits it and expect the same verdict and the same expansion: a written
`transport`, a nested `have` whose body misses, and `close()`, at the linear
frontier, in a focused arm, in a `with` scope, in a pure theorem script and
after execution. Each remaining difference becomes either an agreeing pair or
a documented refusal with a diagnostic that names the context. Keep every
existing expansion round-trip regression.

## Acceptance criteria

- `with` scopes, explicit pure and smart-search scripts and loop
  initialization apply written tactics through the shared frontier function
  or one shared script interpreter, with admission declared in
  `SourceContext`.
- `PostExecutionTactic` is removed, or each remaining variant is justified
  in this file.
- The grouped closure search focuses claims through the same claim
  path as the single-step closers, and `finish_ordered_proof` shrinks to the
  context-specific setup and teardown.
- `docs/reference/tactics/index.md` states any remaining context-specific
  behavior.
- The gate, the nightly corpus and the expansion audit show no verdict
  changes. Any change that does appear is filed and explained.
