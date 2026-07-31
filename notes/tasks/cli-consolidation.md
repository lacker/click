# CLI consolidation: shared helpers, whole-file verify, robust profile parsing

Status: done (2026-07-30)
Claimed: worktree-agent-a861581d5f93ae923 2026-07-30

Scope (design-review item 12 residue + honorable mention; one tooling
agent can own all three):

1. Duplicated helpers: parse_source_location / parse_duration /
   format_duration / the child-watchdog loop exist 3–4 times across the
   four binaries with drifted semantics (audit's inline location parser
   skips one-based validation; mdtests rejects bare-number durations
   the binaries accept). Consolidate into src/cli (some already moved —
   audit uses click::cli helpers; sweep the rest).
2. No whole-file verify CLI: click-verify takes
   file[:line:column]; the docs' "apply the output and run normal
   verification" needs a whole-file/project mode (click-verify PATH
   with no suffix already does whole-file — verify that covers the
   documented workflow, and add a project/directory mode if not).
3. click-profile parses its child's stderr by exact whitespace field
   counts (parse_started_step/parse_finished_step); format drift yields
   silent false-green reports. Either version the timing-line format or
   parse defensively with loud errors. Note 2026-07-30: new timing line
   kinds (contract execution/claims, per-claim) were added; confirm the
   profiler ignores them cleanly today.

Done when: helpers exist once, the documented workflow is runnable
verbatim, unknown/malformed timing lines are an error or a counted
warning rather than silence, and all three gates stay green.

## What was actually found

The two named divergences were already fixed before this pass:
`click-audit::parse_source_location` (click-audit.rs:302) is now a thin
wrapper that delegates to `cli::parse_source_location`, so the
one-based validation is no longer skipped, and `tests/mdtests.rs`
already imported `cli::parse_duration`, so it accepts bare-number
durations exactly as the binaries do. What remained duplicated was in
the test harnesses, not the binaries.

## Part 1 — helpers consolidated (commit "Sweep the last duplicated…")

Moved into `src/cli.rs`, removing the last two copies of each:

| helper | was duplicated in | decision |
| --- | --- | --- |
| `indented_output` | tests/mdtests.rs, tests/examples.rs | byte-identical output preserved |
| `duration_from_env` | `mdtest_time_limit`, `example_time_limit` | parses via `cli::parse_duration`, so both harnesses now accept every spelling the binaries accept |
| `isolated_test_command` | both harnesses' `Command` construction | identical, including `RUST_MIN_STACK=67108864` |
| `run_isolated` + `IsolatedRun` | both harnesses' watchdog loop | messages parameterized so the printed text is unchanged |

Deliberate semantic decisions when copies disagreed:

- **One-based locations win.** Every binary now rejects line 0 and
  column 0; the audit's old permissive inline parser is gone.
- **Bare numbers stay seconds.** `parse_duration("7") == 7s` is the
  accepted input format of four shipped binaries and appears in
  documented command lines, so the harnesses were widened to match the
  binaries rather than the binaries narrowed to match the harnesses.
  Zero durations remain rejected everywhere.
- **click-audit's session worker was NOT folded into `run_bounded`.**
  It is a long-lived bidirectional protocol child (mpsc +
  `RecvTimeoutError`, request/response framing over stdin/stdout), not
  a bounded one-shot. Sharing the two would weaken both. It already
  kills and reaps, per the CLI-watchdog invariant.

## Part 2 — whole-file verify (commit "Give click-verify a directory…")

`click-verify PATH` already did whole-file verification, so the
documented "apply the output and run normal verification" step was
runnable for one sidecar. Two real gaps:

- No doc mentioned `click-verify` at all (`grep -rn click-verify docs/`
  returned nothing before this change).
- No project/directory mode, so the workflow did not scale past one
  sidecar.

Both closed. `click-verify DIR` reuses `cli::find_projects`, so
discovery matches click-audit and click-profile: the directory itself
when it holds sidecars, otherwise each immediate subdirectory that
does. It prints each sidecar as it passes. Whole-file failures now name
the failing sidecar. `docs/advanced/testing-click.md` gained a
"Verifying one file or project directly" section spelling the
expand/apply/verify loop as three pasteable commands.

Location arguments still shape-match first
(`cli::looks_like_source_location`), so a directory name can never be
read as a `PATH:LINE:COLUMN`.

## Part 3 — profile parsing (commit "Classify every click timing: line…")

**Confirmed first**: the 2026-07-30 kinds (`contract execution`,
`contract claims`, `claim`, plus `claim paths` and `function`) are
ignored cleanly today — `parse_finished_step` required
`fields[2] == "tactic"`, which none of them satisfy. But they went down
the same silent `else` that would swallow genuine drift, so the
correctness was accidental, not designed.

Inventory of every `click timing:` kind in the tree (grep
`"click timing:"` under `src/`):

```
source <path>                                   click-profile --child
started tactic <9 fields>                       proof.rs
tactic <9 fields> <elapsed>s                    proof.rs
function <name> <elapsed>s                      lang/click.rs
contract execution <name> <elapsed>s            lang/click.rs
contract claims <name> <elapsed>s               lang/click.rs
contract entry resources do not …               kernel/api.rs (x2)
claim paths <name> prepared <n> in <elapsed>s   kernel/api.rs
claim <name> <key:?> <elapsed>s                 kernel/api.rs
```

Now classified into three buckets:

- **Depended-on** (`source`, `started tactic`, `tactic`): a line of one
  of these kinds that does not parse is a **hard error** naming the
  line and pointing at the parser. Drift here is a false green, not a
  warning, so it must stop the run.
- **Recognized-and-skipped** (`IGNORED_TIMING_KINDS`): listed
  explicitly so a genuinely new kind stands out instead of blending in.
  Keep this list in sync with the emitters.
- **Unrecognized**: counted per kind with one verbatim example,
  printed under `UNRECOGNIZED TIMING LINES`, and it suppresses the
  clean-green `NEXT:` line in favor of one saying the report is not
  trustworthy.

**Chose defensive parsing over versioning the lines.** The emitters
live in `src/lang/click/proof.rs` and `src/kernel/api.rs`, which are
outside this lane and under concurrent edit; a parser that tolerates
whatever they emit while reporting what it does not understand is the
change that keeps working when they move. If someone later wants a
version line, it composes: it would arrive as an unrecognized kind and
be reported, not swallowed.

Kind keywords match at a word boundary and tolerate repeated
whitespace, so `tactic` cannot silently match a future `tactical` kind.

## Repro commands

```
cargo nextest run --lib            # 468 passed, 7 skipped
cargo test --test mdtests          # ok, ~11 s
cargo test --test examples         # ok, ~19 s
cargo nextest run --bins           # 24 passed (NOT covered by the --lib gate)
cargo run --quiet --bin click-profile -- examples/input-cursor
cargo run --quiet --bin click-verify -- examples/input-cursor
cargo run --quiet --bin click-audit -- --max-sites 3 examples
```

Corpus check: profiled input-cursor, jsonc-refcount, and owned-string;
zero unrecognized timing lines across all three, and owned-string still
surfaces its two real 3.4 s smart candidates plus its verification
failure.

## Note for the next agent

`cargo nextest run --lib` does **not** run the binaries' `#[cfg(test)]`
modules, where most of the CLI tests live (24 of them now). Run
`cargo nextest run --bins` as well when touching `src/bin/`.
