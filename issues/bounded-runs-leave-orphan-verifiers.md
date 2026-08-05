# Kill complete verifier process groups on bounded-run timeout

## Problem

After several timed `click-profile` and interrupted verification runs, nine
`target/debug/click-verify examples/owned-vector/vector.click` processes were
still running. The oldest had consumed CPU for roughly two and a half hours.
One stale wrapper shell also remained. Later profiles and tactic-budget tests
ran under that load and produced false performance failures.

`run_bounded_with_input` currently calls `Child::kill()` on only the immediate
child. When that child is a wrapper that spawned a verifier, the descendant
keeps running and retains inherited output pipes. A timeout is not complete
until the entire spawned process tree is terminated and reaped.

This is the highest-priority tooling issue: leaked workers make every subsequent
performance result untrustworthy and consume user resources after the command
appears finished.

## Intended design

- The self-reexecuting profile, expand, audit, and fixture wrappers are now
  removed. Ordinary deadlines run inside the shared engine and do not require
  a child process.
- For the smaller set of workers retained solely for crash/stack-overflow
  isolation, start the direct Click worker in a new process group/session on
  Unix.
- On timeout or parent-side error, terminate the whole group, wait briefly, then
  force-kill and reap any survivors.
- Ensure stdout/stderr reader threads cannot wait forever on pipes held by
  descendants.
- Provide the equivalent child-tree behavior on supported non-Unix platforms,
  or document and test a platform-specific fallback.
- Keep exact target scoping: never signal the caller's process group.

Do not resolve this issue by adding another shell, test-binary, or CLI wrapper.
Process-group cleanup is a safety rule for the isolation that remains after the
direct-engine migration.

## Regression

Add a test helper that spawns a child which itself spawns a long-lived
grandchild holding inherited stdout/stderr open. Bound the wrapper to a short
duration. Assert that `run_bounded` returns promptly, both child PIDs cease to
exist, the pipes close, and a subsequent bounded run is unaffected.

Also test normal completion so process-group setup does not kill successful
descendants prematurely.

## Acceptance criteria

- No verifier descendant survives a profiler, audit, fixture, or expansion
  timeout.
- Timeout returns only after the process group is terminated and output readers
  are joined.
- Regression tests cover wrapper, grandchild, inherited pipes, and normal exit.
- Performance measurements are rerun from a confirmed clean process state after
  the fix.
