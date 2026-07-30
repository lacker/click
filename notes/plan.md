# Short-term plan

Last updated: 2026-07-30 (later session). This is the working list of
near-term tasks — things doable now without big syntax expansions or
resource-logic changes. Larger arcs are listed at the bottom so they
don't get lost, but they are not part of this plan.

Current baseline: **master is green** on all three default gates
(lib 465/465 via `cargo nextest run --lib`, mdtests 264 visible via
`cargo test --test mdtests`, examples via `cargo test --test examples`).
Keep it that way: every change validates all three gates before landing.

## 1. Make profile / expand / audit work, then fix what they find

The proof-performance workflow (`click-profile`, `click-expand`,
`click-verify`, `click-audit`) should be routinely usable. The settled
design invariants and the working rules live at the bottom of this file.

**2026-07-30 session results (decide-memo commit):** kernel `decide`
searches were re-answering ~500 distinct conditions thousands of times
each. Decisions are now memoized by fact-set content identity (see
`src/kernel/assumptions.rs`; `CLICK_DISABLE_DECIDE_MEMO` bypasses it for
A/B). Measured: input-cursor whole-file verify 30+ min → ~9 s; audit
session init >1 m timeout → ~11 s; full mdtest suite ~12 s; full
`click-profile` across examples completes in ~2 min. The old frontier
list below is updated from a fresh profile.

Order of attack, one frontier at a time, commit each independently:

1. **input-cursor: DONE 2026-07-30.** Whole-file verification passes in
   ~15 s and the example is de-quarantined (verifies inside the
   examples gate). Six pre-existing layers were fixed, all confirmed
   pre-existing via `CLICK_DISABLE_DECIDE_MEMO` A/B: (a) certificate
   premises must strictly replay-lower before emission; (b)
   pointer-typed loads of framed int32 cells fall through to symbolic
   loads during composite expansion; (c) the bounded order prover
   bridges load endpoints through effect-summary framing; (d) equality
   claims resolve both sides to constants via the bounded normalization
   walk; (e) `var == load` ensures certify by walking one equality fact
   to its load spelling, matching pointer-offset atoms transitively
   over the PointerOffsetEqual fact graph with snapshot-bridged load
   equality, and requiring the cell framed between snapshots
   (`certification_proves_equality_via_load_fact` in api.rs). Owner
   decision 2026-07-30: certificate/implementation details do not need
   sign-off; only Surface Click semantics changes do.
2. **Audit `by auto` re-expansion** : audit sites 28–30 (jsonc-refcount,
   all `by auto`) fail re-expansion with "no explicit C proof tactic
   starts at 10:6" — expansion rewrites `auto` into a by-block, so the
   original cursor no longer points at a tactic. The byte-identical
   re-expansion check needs position remapping for rewritten sites.
3. **Slow simple tactics** (fresh profile, 120 s limit): input-cursor
   shared_pipeline `step` 5.4 s (statement 7; likely same snapshot
   blowup as item 1), owned-split-buffer pipeline `step` 577 ms.
4. **Slow smart tactics** (fresh profile): owned-split-buffer
   execute_rest 14.3 s, input-cursor execute_rest 12.2 s, owned-string
   execute_step 5.4 s and have 5.1 s. Expand each, apply, reverify.
5. **Full audit**: `cargo run --quiet --bin click-audit -- examples` to
   completion (now feasible: bounded runs finish in minutes). Fix
   concrete bugs immediately; treat timeouts as performance bugs; stop
   for discussion before changing certificate semantics; resume with
   `--start-at`.
6. **One-gateway check**: after the corpus audit is green, one bounded
   code audit that every smart success commits through TacticCertificate
   replay with no bypass. Not an open-ended refactor.

Done when: profile shows no SIMPLE >500ms / SMART >2s across examples,
the audit completes every inventoried site with idempotent byte-identical
rewrites, and child cleanup is confirmed after every watchdog kill.

## 2. De-quarantine backlog

Quarantine entries are explicit and temporary; shrink the lists.

- **mdtests** (`tests/mdtests.rs` QUARANTINED, 6): four item-7 entries
  (bubble_pass3, bubble_sort3, composite_owner_buffer_field_dependent,
  fill_tail_keeps_first) plus the two named-memory-states residue entries
  (vector_fill, field_derived). Re-test the four item-7 entries against
  current master — recent certifier gains may have moved them. The two
  residue entries are blocked on the named-memory-states arc (below);
  don't burn time re-bridging them (see canonical-memory.md for the
  exhaustion evidence and branch `claude/forall-extension-wip`).
- **examples** (`tests/examples.rs` QUARANTINED, 5): last sweep
  (early 2026-07-30): owned-string fails a loadability have, owned-vector
  times out at 600 s, owned-split-buffer fails a call-precondition VC.
  Each is its own investigation; the profile/expand/audit ladder above
  will touch the same code paths.
- **lib** (7 `#[ignore]` expansion tests): expansion-era failures
  (expands_nested_branch_tactic_by_source_location,
  expansion_preserves_unfolded_resource_and_predicate_fact_spellings,
  execute_rest_return_certificate_omits_unused_ambient_facts,
  execute_step_expands_call_assign_fact_from_internal_snapshot,
  verifies_opaque_predicate_from_requirement,
  verifies_old_memory_loop_invariant,
  expands_grouped_immutable_read_with_multiple_claim_successors).
  These overlap heavily with the expand/audit work in section 1.

## 3. Small design-review items

From `design-review.md` (see it for full context). The big-ticket items
(1–3 soundness, struct padding, parser comments/unary-minus/initializers)
were fixed earlier; layout-slot field ownership landed 2026-07-30. What
remains that is small-ish:

- **Duplicated helpers across the four binaries** (item 12):
  parse_source_location / parse_duration / format_duration / watchdog loop
  exist 3–4 times with drifted semantics. Consolidate into one module.
- **No whole-file verify CLI** (item 12): `click-verify` demands
  file:line:column; add a whole-file/project mode so the documented
  workflow is runnable.
- **click-profile parses its child's stderr by whitespace field counts**
  (honorable mention): format drift silently yields false-green reports.
  Make the timing stream a stable format or parse defensively with errors.
- **35 panic!/unreachable! sites in proof.rs reachable from user input**
  (honorable mention): convert the reachable ones to diagnostics.
- **while-invariant rule checks preservation in one fork context**
  (honorable mention): currently test-only but exported; fix or fence.
- **Doc vocabulary churn** (honorable mention): stale tactic synonyms,
  close_invariants missing from the tactic inventory, "legacy spelling"
  self-reference. One docs pass.
- **Remaining parser ergonomics** (item 4): verify current status of
  required-else and `a->b->c` chains; fix if small, otherwise leave for
  the language arc.

## 4. Small recent follow-ups

- **Grouped-simp candidate-loop perf**: `atomic_derivation_premises`
  clones the whole Assumptions per candidate and re-proves.
  field_derived spends ~500 s there even to fail. Pre-filter candidates
  by base-block relevance or restructure the loop. (Also gates the
  field_derived de-quarantine.)
- **Lib suite pace**: after the canonical/resolution equality arms, one
  lib test occasionally reports slow (>10 s threshold). Keep an eye on
  `cargo nextest run --lib` output; if a test goes slow consistently,
  profile the new arms' cost there.
- **Repo hygiene** (ask the owner before deleting): stale branches
  (claude/engineering-debt and claude/store-provenance are merged;
  claude/code-review-design-issues-763cd1, codex/click-expand,
  wip/tactic-certificates-2026-07-18, worktree-claude are older),
  worktrees under .claude/worktrees/, a `store-provenance WIP` stash
  (byte-identical to the merged branch's first commit, safe to drop once
  confirmed), and stale /private/tmp worktrees (click-head-audit,
  click-head-probe, click-p0-baseline).

## Settled design invariants (from the old todo.md — keep honoring)

- TacticCertificate is the smart/simple boundary; a smart success must
  replay through a surface-expressible certificate before acceptance.
- Expansion emits the exact accepted certificate — no second proof
  search, no generic fallback.
- Simple tactics are deterministic replay and must be fast; don't hide a
  slow simple tactic by expanding an enclosing smart tactic.
- ProofSite + one-based PATH:LINE:COLUMN are shared by verification,
  profiling, expansion, auditing, and rewriting.
- click-expand emits a rewritten sidecar and does not reverify it;
  verification and auditing stay separate composable operations.
- Kernel Click has no textual syntax; all output is documented Surface
  Click accepted by the ordinary parser. Canonical struct spellings are
  `owner->field`, `(owner->pointer_field)[start..end]`, `object(owner)`;
  `load_*` / `byte_offset` are escape hatches only.
- CLI watchdogs must kill and reap their children.
- Everything the certifier consumes gets a surface spelling (owner
  decision 2026-07-30).

## Working rules

- Validate all three gates before landing; keep master green.
- Fix correctness bugs before continuing any sweep.
- Reproduce stale timing claims before acting on them.
- One frontier at a time; commit each independently verified fix.
- Probe pattern: env-gated eprintln/file dumps at the failing check, run
  with MDTEST_FILTER, strip probes before committing.
- Guard and depth-gate any new recursive prover arm: three separate stack
  overflows in 2026-07-30 work all traced to structural recursion on deep
  terms (the harnesses now give children 64 MB stacks, but that is a
  backstop, not a license).
- SOUNDNESS TRAP: never drop havoc/call-havoc blocks from canonical load
  memories; kernel test
  memory_load_equality_does_not_ignore_loop_havoc_identity guards this.

## Larger arcs — explicitly NOT short-term

- **Named memory states (option C)**: the representation rewrite that
  clears the two residue mdtests, likely most of the quarantine backlog,
  and the perf class. Design sketch and decision record in
  `canonical-memory.md`.
- **Language-design proposals** (write-only proofs, verbosity/abstraction,
  memory-concept families): `language-proposals.md`. Parked.
- Anything expanding surface syntax or changing resource logic.
