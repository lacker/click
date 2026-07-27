# `click-profile` / `click-expand` Handoff

Last updated: 2026-07-26

## Goal

Make proof automation an explicit performance trade:

- smart tactics may search;
- every successful smart tactic must produce a surface-expressible
  `TacticCertificate`;
- ordinary verification must replay that certificate without repeating smart
  search;
- `click-expand` must replace the selected source proof site with the same
  certificate that verification accepted;
- the rewritten source must verify normally and re-expansion must be
  byte-identical.

There must not be a second class of internal-only successful proof steps or a
fallback that guesses a different proof during expansion.

## Current architecture

### Certificates

`TacticCertificate` is the strict smart/simple boundary. It recursively permits
only source-expressible simple tactics and control-flow structure. Successful
smart tactics plan a certificate, validate it, replay it through the ordinary
proof executor, and commit only the replay result.

The certificate boundary currently covers:

- grouped and individual function claims;
- smart `have` and smart theorem application;
- pure theorem proofs;
- loop initialization and preservation, including omitted phases;
- structural assertions;
- whole-loop and step structural effects;
- statement execution, loop summaries, framing, and fact transport.

`ProofSite` is the shared identity used by verification, profiling, selection,
and rewriting. It covers function claims, theorem claims, loop phases, and
structural items.

### Source selection

The public command is:

```sh
cargo run --quiet --bin click-expand -- \
  [--time-limit 60s] path/to/file.click:LINE:COLUMN
```

Locations are one-based source coordinates. A location may select:

- one explicit tactic, including a tactic nested in `if` or `advance`;
- a one-token smart proof such as `by auto`;
- an omitted/default proof;
- a loop initialization or preservation proof;
- a structural assertion or effect proof.

Generated certificate steps inside an implicit/default proof retain their
internal indices for profiler diagnostics, but all map back to the one
selectable source proof site.

Expansion prints the complete rewritten sidecar to stdout. It does not edit in
place and does not run a second verifier after emitting the rewrite. The caller
must apply the output and run normal verification or profiling.

Expansion does replay verification from the start of the sidecar through the
selected proof site. A late selector can therefore take longer than the
selected tactic itself.

### Profiling

Use:

```sh
cargo run --quiet --bin click-profile -- examples
cargo run --quiet --bin click-profile -- --time-limit 30s examples/owned-vector
```

Defaults:

- smart threshold: 2 seconds;
- simple threshold: 500 milliseconds;
- control threshold: 2 seconds;
- project watchdog: 30 seconds.

The output is action-oriented:

- `SIMPLE`: deterministic replay is slow; fix the engine and do not expand it;
- `SMART`: expand the reported source site;
- `CONTROL`: inspect nested timings rather than optimizing the container;
- `TIMEOUTS`: use the active frontier when one was recorded.

The profiler class is emitted by the verifier. Do not infer tactic class from
the tactic name.

Both CLI watchdogs kill and reap their child processes. A timeout is an outer
wall-clock cutoff, not an internal proof result.

## Correctness state

The currently known certificate and source-rewriting bugs have been fixed.
Notable strict boundaries include:

- expansion lowers the exact successful smart plan rather than searching for
  another proof;
- statement certificates preserve distinct call and memory-snapshot
  identities;
- snapshot transport is certified at the mutation boundary;
- materialization-only transports remain internal to statement certificates;
- expanded source contains no hidden ambient premises;
- structural and loop certificates preserve branch/path alignment;
- omitted proofs are inserted canonically;
- profiler locations resolve to source sites that `click-expand` can select;
- expansion capture stops after the selected tactic and does not verify the
  suffix.

Current focused validation:

- 397 library tests pass;
- 7 `click-profile` binary tests pass;
- the owned-string example verifies normally;
- a 10 ms diagnostic owned-string profile completes without source-mapping
  errors;
- the default-threshold 15-second corpus profile reports no completed slow
  simple tactics and no verification failures.

There is no presently reproduced expansion or profiler-coordinate correctness
failure.

## Remaining correctness work

### 1. Global certificate audit

The main missing confidence mechanism is a generated audit over every
proof-bearing source construct.

For every syntactic smart-tactic occurrence, the audit should:

1. verify the original source;
2. identify its `ProofSite` and source coordinate;
3. require construction of a smart-free `TacticCertificate`;
4. replay the certificate through the ordinary executor;
5. expand only that occurrence or proof site;
6. verify the rewritten source from normal inputs;
7. re-expand and require byte-identical output;
8. compare branch/path outcomes where applicable.

The audit must inventory new proof-bearing syntax explicitly so adding a new
surface cannot silently bypass the certificate boundary.

### 2. Seal superseded smart-success APIs

After the global audit is green, remove or make private any direct
smart-success path that can commit proof state without passing through
`TacticCertificate`. Kernel reasoning helpers may remain, but proof-surface
automation must have one gateway.

## Known tooling and performance warts

- The profiler suggests a fixed 60-second expansion watchdog. Prefix replay
  plus smart planning can exceed that even when expansion would eventually
  succeed.
- A project can time out between timed tactic events. In that case the
  profiler currently prints the project timeout without an active frontier.
  Timing coverage should be extended rather than guessing at a tactic.
- Very low thresholds can report several generated steps at the same implicit
  `by auto` source site. This is correct but noisy; expanding any of those rows
  expands the whole implicit proof.
- Expansion replays the sidecar prefix for every request. There is no
  certificate cache or persistent verification session.
- `click-expand` prints the whole sidecar rather than a patch. This is
  deliberate until the certificate audit is complete.

## Current performance frontier

A fresh 15-second-per-project corpus profile on 2026-07-26 reported no
completed simple tactic over 500 ms.

Completed slow smart tactics:

- `examples/owned-vector/vector.click:75:5`
  (`vector_get.contract`, final `simp`): about 10.3 seconds;
- `examples/owned-string/owned_string.click:471:5`
  (`owned_string_pop.contract`, smart `have`): about 5.6 seconds;
- `examples/input-cursor/input_cursor.click:125:5`
  (`input_cursor_take.contract`, `simp`): about 3.8 seconds.

The focused 60-second owned-vector profile now reports:

- one slow simple `apply_loop_summary` replay at
  `examples/owned-vector/vector.click:134:5`, about 528 ms;
- the 10.2-second `vector_get` smart `simp` at line 75;
- a 5.9-second loop-preservation smart `simp` at line 125;
- a 3.4-second `vector_fill` smart `execute_rest` at line 134;
- a timeout in the final `vector_fill` smart `simp` at line 136.

Owned-string still times out at
`examples/owned-string/owned_string.click:485:5`, a final smart `simp` that
takes about 12 seconds in a focused 30-second profile.

The motivating `owned_string_set` successor proof at line 183 is fixed:
planning fell from 63.9 seconds to about 67 ms, and expansion emits a
one-premise arithmetic certificate.

## Next work

Work one frontier at a time and commit each logical change independently.

1. Fix the 528 ms owned-vector `apply_loop_summary` simple replay without
   adding search or special-case fallbacks.
2. Reprofile owned-vector. Expand one smart frontier only after no reached
   simple tactic exceeds 500 ms.
3. Continue the same cycle for
   owned-string line 485, owned-string line 471, and input-cursor line 125.
4. Build the global certificate audit before claiming expansion is complete.

Do not optimize by adding proposition-specific smart fast paths, broad ambient
premises, generic transport fallbacks, or internal-only certificate tactics.
