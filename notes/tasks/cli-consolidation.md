# CLI consolidation: shared helpers, whole-file verify, robust profile parsing

Status: in progress
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
