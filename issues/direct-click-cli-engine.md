# Use one direct Click CLI over one bounded verification engine

## Problem

Click's tools currently wrap and re-execute processes instead of calling one
verification engine directly:

- `click-profile` re-executes itself in a hidden child mode and reconstructs a
  profile by parsing timing text from stderr;
- `click-expand` re-executes itself with `--child` to obtain a wall-clock
  timeout;
- `click-audit` uses private subprocess protocols for retained verification,
  expansion, re-expansion, and cold checks; and
- the example and mdtest harnesses re-execute the test binary as a fixture
  wrapper.

This architecture caused orphan verifiers, misleading timing attribution,
duplicated timeout behavior, unrelated-proof expansion failures, and user-facing
workflows built from `cargo run`, redirects, and `mv`. Users should be able to
ask the Click CLI directly to perform a bounded operation. Higher-level Click
commands should compose a shared API, not wrap other executables and scrape
their output.

## Command design

Provide one installed `click` executable with subcommands:

```text
click verify [--time-limit DURATION] TARGET
click profile [profile options] TARGET
click expand [--output PATH | --in-place] LOCATION
click audit [audit options] TARGET
```

`TARGET` consistently accepts a sidecar, selected source location, project,
examples directory, mdtest, or mdtests directory where the operation supports
that shape. Compatibility binaries such as `click-verify` may temporarily call
the same Rust subcommand function, but they must not spawn the `click` binary or
implement a second engine path.

`click expand --in-place` should expand the selected proof, targeted-verify the
rewrite, and atomically replace the source only on success. `--output` writes a
named artifact without shell redirection. Standard output can remain available
for composition, but documentation and profiler suggestions should use the
first-class safe workflow rather than asking users to patch commands together.

## Engine design

Create a shared `VerificationEngine`/session API used directly by every
subcommand and fixture harness. It should accept:

- a typed target and selected proof unit;
- a deadline/cancellation context;
- tactic-class budgets;
- a structured event sink for phase, tactic, work, and certification events;
- an operation mode: verify, profile, expand, or audit; and
- an output/diagnostic budget.

Profiling consumes structured events in memory; it does not parse stderr.
Expansion returns a checked rewrite artifact; it does not re-execute the CLI.
Audit retains an engine session directly and invokes the same expansion and
targeted-verification APIs.

OS process isolation may remain only where it materially contains a stack
overflow or crash. It is an internal boundary around a direct Click worker, not
the mechanism for ordinary deadlines, profiling, or command composition. Any
remaining isolated worker must be one owned process group and must be cleaned up
completely.

## Migration order

1. Define target parsing, deadlines, structured events, and bounded diagnostics
   in the shared engine API.
2. Add the unified `click verify` command and make tests call the same API or
   direct CLI worker.
3. Move profile to structured in-process events and delete its self-child mode
   and stderr timing parser.
4. Move expansion to the direct engine and add checked `--output`/`--in-place`.
5. Move audit's retained session and cold comparisons to the shared APIs.
6. Keep compatibility binaries as thin, non-spawning dispatch shims, then
   remove them when documentation and scripts use `click <subcommand>`.

## Regression

- Test each subcommand through its Rust entry function and the installed CLI.
- Assert no normal verify/profile/expand operation calls `Command::new` or
  `current_exe`.
- Run a bounded timeout fixture and assert no descendant remains.
- Expand in place, deliberately fail verification, and assert the original file
  is unchanged; then pass and assert atomic replacement.
- Compare verify, profile, expand verification, and audit results for the same
  selected unit and require identical checked outcomes.

## Acceptance criteria

- Users can perform the complete workflow with `click` subcommands and no
  `cargo run`, shell redirect, temporary-file move, or wrapper script.
- Verify, profile, expand, audit, and fixture gates use one verification engine
  and one target model.
- Deadlines are enforced in the engine rather than by self-reexecution.
- Profile consumes structured events, not stderr text.
- Expansion can safely verify and atomically apply its own rewrite.
- Remaining process isolation is explicit, minimal, and leak-free.
