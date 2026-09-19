# HANDOFF: C++ destructor-as-step (try-descent) work

**Status: INCOMPLETE PROTOTYPE. Tree is RED (gate fails). Do NOT integrate.**
Worktree: `/private/tmp/click-cleanup-steps`, branch `codex/cleanup-steps`
(compared against primary `master`; all work uncommitted at handoff time
except as noted below — check `git status` first; the notes file itself
(`HANDOFF-TRY-DESCENT.md`) is scratch and must be DELETED before any
integration, along with all `mdtests/zz_*.md` probes.)

## 1. What this session was about

P1 issue `issues/control-flow-demo.md`, Program 2: verify a C++ cross-call
exception with two RAII guards (`mdtests/cpp_two_guard_unwind.md`, parked
`expect fail`). It fails on `second_cell[0] == old(second_cell[0])`:
two guards over two distinct cells, second cell modeled as an offset of the
first (`load(first_cell[(v100001 - v100000)])`), framing across the first
guard's destructor store needs offset disequality.

The user-directed goal for THIS workstream: make each implicit C++
destructor call its own surface step — addressable by normal `step()` /
`mark` / `at()` machinery, no synthetic keys, no probe-specific automation
tuning ("magic"). Rationale: guard-at-cleanup-entry facts (`second.pointer
== second_cell`, `second.saved == old(second_cell[0])`) are unnameable today
because (a) guard locals are dead at function outcome (`UnboundVariable`),
and (b) there is no reachable program point at implicit destructor entries
to hang an `at()` on.

## 2. Robust empirical findings (trust these)

- **The `try` is NOT the trigger.** Plain two-guards-over-distinct-cells
  (no `try`, no throw, no helper — `zz_verify_plain.md` shape) fails with
  the IDENTICAL diagnostic. Verified with explicit FAIL + full message,
  multiple runs. By contrast: one guard (plain or `try`) passes; two guards
  over the SAME cell (`restore_twice` fixture) passes; one guard + `try` +
  untouched second cell passes. So the defect is: two guards over two
  DISTINCT cells where the second cell's restoration must be proved.
- **Layout fact:** `SourceExecutionLayout::for_function` treats a whole
  `TryCatchInt32` as ONE atomic `Plain` statement (`source_layout.rs`
  visitor descends `Seq`/`If` only). Verified by temporary print (since
  removed): `guarded2` body indexes as exactly 2 statements (outer try,
  final return). A single surface `step()` therefore reaches function exit.
- **Stepping IS granular once descended:** with the layout+entry changes
  below, `trynothrow` (try, no throws) walks constructions → cleanups →
  return in 7 steps, kernel evidence accepts each (no source-order
  refusals). No fork/routing involved (nothing throws).
- **Guards ARE nameable while live** (in plain scopes AND descended-try
  interiors): `have first.pointer == first_cell`, `have second.saved ==
  ...`, `have first.pointer == second.pointer` all lower (the false ones
  correctly fail to *prove*; only some fail to *lower* — see §4).
- **Grouped-driver planning fuses tactics.** `step(); execute();` vs
  `step(); step();` behave differently (the driver plans jointly), so naive
  step-counting probes are unreliable. Always verify with full proofs, and
  distrust any earlier "PASS" reading obtained only by absence of a failure
  substring — several such readings in this session's history were grep
  artifacts on files that never imported (missing `noexcept` under
  `normal_only`) or had broken fences. Robust check pattern used later:
  look explicitly for `test result: ok` vs `test result: FAILED`.

## 3. What is built (all in worktree, uncommitted)

- `src/surface/lowering/source_layout.rs`
  - New `SourceStatementKind::Try { try_statement_index,
    handler_statement_index, after_try_statement_index }`.
  - `for_function` visitor descends `TryCatchInt32` (body then handler),
    patches `try_body_last.continuation → after_try`. C layouts contain no
    `TryCatchInt32`, so C layouts are byte-identical by construction.
  - Two exhaustive-match sites updated (`cursor_execution.rs`,
    `surface_construction.rs`: `Try → None` alongside `Plain|If`).
- `src/kernel/proof/execution.rs`
  - `ExceptionalContinuation { binding, handler, handler_first_index }`
    (exported via `kernel/proof/mod.rs` → `surface/proof.rs`).
  - `ProofExecutionContinuation.exceptional: Option<...>` (+4 construction
    sites with `None`).
  - `EvidenceTryFrame` + `evidence_try_stack` on `ExecutionProofCore`.
  - `try_evidence_source_after()` + hook into `check_statement_evidence`
    (now `&mut self`): descent-accept / binding micro-steps / handler-head
    / normal-exit rules, ALL firing only where linear matching fails
    (mismatch-gated for safety). Plus a `running_state` Cow→owned tweak
    for borrowck.
- `src/surface/proof/cursor_execution.rs`
  - Transparent try-descent loop in the shared step function (push handler
    continuation, splice try body, re-split; nested trys compose).
  - `route_throw_to_handler()` helper (pop-to-handler with unwind-abandon
    semantics, binding declare+assign via certified micro-transitions with
    evidence recording, handler entry positioning + snapshot).
  - Hook in the single-`Throw` commit arm (falls through to shared
    epilogue on success).
  - `fork_throwing_call_in_try()` + hook in `bounded_execute` worklist
    (precompute transitions, validate exactly `{Normal, Throw}`,
    Normal-commit mirrored, Throw routed on clone, push both).
  - TEMPORARY DEBUG eprintlns (MUST REMOVE): `CLICK_DEBUG_FORK` prints in
    the fork hook, both worklist loops (`WORKLIST-BOUNDED-LOOP`,
    `WORKLIST-REST-LOOP`), and at the multi-transition error
    (`STEP-ERROR-HERE`).
- `src/surface.rs`, `src/surface/proof.rs`: import threading
  (`c_declare`, `c_assign`, `ExceptionalContinuation`).
- Probes (untracked, all scratch — DELETE before integrating; several
  have mangled histories, do not trust without rewriting):
  `mdtests/zz_*.md` (plain-guard, try-plaincell, trynothrow, let-capture,
  verify-plain, c-local-guard, req variants from the earlier C-repro
  worktree — note: `codex/resource-addr-repro` worktree may still exist
  with more).

## 4. Open problems (in order)

1. **Fork is in the wrong layer (BLOCKER).** `fork_throwing_call_in_try`
   lives in `bounded_execute`'s worklist, but real proofs never go there:
   instrumented runs show zero worklist iterations — `execute()`/`step()`
   run through proof-object application
   (`apply_execution_statement_step_with_policy`, 27 hits) into the shared
   step function. The one-guard test still fails at the shared function's
   multi-transition error. The fork (or equivalent {Normal,Throw}→arms
   handling with handler routing) must live where proof-object steps
   fork — likely mirroring branch/if planning nodes or the switch fork —
   NOT in the cursor worklist. The switch-fork clone pattern and the
   `selected_path_fact` mechanism are the two candidate shapes; neither
   has been validated for call outcomes.
2. **`have second.pointer == second_cell` won't lower** ("kernel
   lowering produced 0 paths"). Established: int fields fine, pointer
   self-equality fine, field-vs-field pointer fine; ONLY loaded-field vs
   parameter pointer equality fails (reproduced in plain C with local
   structs too, so not C++-specific). Without this, explicit proofs can't
   cite the bridging equality even where guards are nameable. Separate,
   precise, small-looking gap — investigate `have`-lowering of pointer
   equality across blocks.
3. **`have at(...)` declined** by grouped driver ("proof-shape
   limitation... grouped execution must still form one transition") —
   observed twice, unresolved; may be moot if plain `have`s suffice.
4. **Grouped planning fuses step sequences**, so black-box step counting
   is unreliable; validate with complete proofs only.
5. Joins with non-equal try stacks, `pending_exceptional_call`
   interplay, expansion/profiling churn: designed around but untested.
   `have-at` driver, `outcomes`-mid-execution NOT built (deferred;
   may be unnecessary).

## 5. Repro commands (from repo root of THIS worktree)

- Baseline P1 probe (still parked fail):
  `CLICK_CPP_EXPORTER=/Users/lacker/click/target/cpp-exporter/click-cpp-exporter MDTEST_FILTER=cpp_two_guard_unwind cargo nextest run --test mdtests --no-capture`
- Minimal plain repro (no try; same diagnostic): write `zz_verify_plain.md`
  per §2 (noexcept + normal_only!), run same way.
- Focused suites: `cargo nextest run --lib surface::tests::diagnostic_tests`,
  `cargo nextest run --test mdtests`, full gate `scripts/check.sh`
  (needs `RUST_MIN_STACK=8388608`, pinned LLVM exporter; currently RED).
- `CLICK_DEBUG_FORK=1` enables the temporary traces.

## 6. Suggested next steps for the new agent

1. Delete scratch (`HANDOFF-TRY-DESCENT.md`, `mdtests/zz_*.md`, debug
   eprintlns) only AFTER extracting what's needed — or keep worktree as
   lab and start a fresh branch from master.
2. Decide fork placement by reading proof-object split/branch code
   (`splits_and_scopes.rs`, `CallOutcomes` planning nodes) rather than
   cursor worklists.
3. Independently fix the pointer-equality lowering gap (§4.2) — it blocks
   explicit proofs with or without descent and is falsifiable fast.
4. Re-run the FULL `scripts/check.sh` gate before any integration;
   per AGENTS.md integrate only a coherent green commit via a fresh
   branch, never this scratch state.

## 7. Thread history (why things look the way they do)

- Started from `issues/control-flow-demo.md` P1 two-guard probe; first
  improved the identical-load diagnostic (merged), then the unclosed-goal
  context dump (merged) — both on master already.
- Chased a C reduction (worktree `codex/resource-addr-repro`, may still
  exist): found same-*symptom* C failures, all closable with explicit
  steps — i.e. automation gaps, not the defect. Lesson: symptom match ≠
  root-cause match.
- User directed try-descent ("destructor as extra step; no magic; no
  synthetic keys; continue working"). Investigation showed: layout treats
  try as atomic (verified by print); suffix fusion also swallows
  try+return; kernel evidence tracks source order independently (must
  mirror descent); fork-on-throw has no existing home (pending split is
  terminal-by-contract + empty-continuations-gated).
- Session ended when fork placement hit the driver-layering problem
  (§4) — that is the precise blocker, not general diffusion.
