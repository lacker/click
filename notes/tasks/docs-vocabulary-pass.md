# Docs vocabulary pass

Status: done (2026-07-30)
Claimed: worktree-agent-ae547bd447d583266, 2026-07-30

Scope (design-review honorable mention): one documentation pass over
docs/ fixing tactic-vocabulary churn:
- "execute_rest() is legacy spelling for execute_rest()"
  self-reference (separation-logic.md:265 at review time).
- close_invariants() used in examples but missing from the tactic
  inventory.
- ~30 tactics with near-synonym clusters
  (step/execute_step/execute_until/execute_rest/...) — document the
  canonical set and mark the synonyms.
- While in there: confirm docs/advanced/testing-click.md reflects the
  2026-07-30 click-audit behavior (slow-site limit, run time limit,
  once-per-claim cold reverify, claim-based fixed point).

Done when: the tactic inventory is complete and self-consistent and the
audit docs match the binary's USAGE text.

## What landed

Docs-only; no .rs file touched. Gates all green (465 lib, mdtests,
examples).

1. separation-logic.md: the self-referential sentence was a blind
   `symbolic_execute` -> `execute_rest` rename in commit 2ebbe59
   ("cleanups"). Original text (9ca6330) read "`symbolic_execute()` is
   now best understood as legacy spelling for `execute_rest()`".
   Restored the meaning; parser.rs:1877 maps `symbolic_execute` to
   `ProofTactic::ExecuteRest`, confirmed by CLICK_TIMINGS printing
   `execute_rest class smart` for a `symbolic_execute()` script.
   The same rename corrupted a SECOND spot, separation-logic.md:190
   ("after `execute_rest()` / `execute_rest()`"); fixed too.
2. `close_invariants()` was absent from all of docs/, not just the
   inventory. Added to proof-tactics.md (simple table + its own
   section), proof-workflow.md, basic/proofs-and-proof-scripts.md, and
   intermediate/loops-and-invariants.md. Grounded facts: simple class;
   only inside `preserve by { ... }`; at most once per path; optional,
   because Click appends the closer implicitly and the certificate
   carries an explicit leaf either way.
3. Added a "Synonyms And Legacy Spellings" section to proof-tactics.md
   with the true-synonym table, the look-alike-but-different table, and
   the internal names that appear in CLICK_TIMINGS but have no surface
   spelling. Added a "Where Each Tactic Is Available" section
   (function / theorem / initialize / preserve), read off
   validate_pure_theorem_tactics and validate_loop_initialization_tactics.
4. testing-click.md audit section rewritten against
   `click-audit --help` and src/bin/click-audit.rs.

## Doc bugs found beyond the brief

- proof-tactics.md listed bare `apply(theorem(args))` and bare
  `transport(source, target)` in the SIMPLE table. `ProofTactic::class()`
  makes both SMART; only the `using { fact ...; }` spellings are simple.
  Verified with CLICK_TIMINGS: bare apply prints `class smart`, the
  `using` form prints `class simple`. Lib test
  `parses_and_classifies_simple_and_smart_tactics` asserts the same.
- The theorem-proof tactic list in click-language.md and
  basic/proofs-and-proof-scripts.md was missing intro / conjunction /
  left / right / double_negation / vacuous / contradiction / derive /
  calculate / apply-using / proof-level `if`, and did not say that
  `by frame;`, `have`, `witness`, `choose` are rejected there.
- loops-and-invariants.md described `initialize` as accepting "apply,
  have, if, unfold, simp"; the real allowlist also has assumption,
  normalize, rewrite and nothing else.
- click-expand's optional `--time-limit` was undocumented.
- click-verify was not mentioned anywhere in docs/; added a short
  subsection covering its `:LINE:COLUMN` targeted mode.

## Findings (no code changed)

- No documented behavior was found that the code fails to implement.
  Every mismatch in this pass was the docs being wrong about the code.
- STALE QUARANTINE REASON (not my lane): tests/examples.rs lists
  owned-vector as "whole-file verification exceeds 10 minutes". It now
  fails fast: `./target/debug/click-verify
  examples/owned-vector/vector.click` exits 1 in ~12.5 s with
  "`vector_fill.loop(0).preserve` invariant bundle: could not replay
  invariant closer: invariant 1 is missing path goal: ForAll ...".
  That matches notes/tasks/store-provenance-family.md, which already
  records "Fails in ~12 s (was a 600 s timeout)"; only the QUARANTINED
  reason string is out of date. Whoever owns tests/examples.rs should
  update it.
