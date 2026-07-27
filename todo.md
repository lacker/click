# `click-profile` / `click-expand` / `click-audit` Handoff

Last updated: 2026-07-27

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

### Location-targeted verification

Use:

```sh
cargo run --quiet --bin click-verify -- path/to/file.click:LINE:COLUMN
```

The verifier parses and validates the complete sidecar, resolves the location
to its containing theorem or C function proof, and verifies only that semantic
unit. C-function targets also verify their transitive C-call dependencies.
Unrelated function proofs are not executed.

`click-audit` uses this mode for rewritten sidecars. Original project discovery
still performs one complete verification so the audit never treats an
unverified baseline as authoritative.

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

- 407 library tests pass;
- 7 `click-profile` binary tests pass;
- 6 `click-audit` binary tests pass;
- the `execute_rest` order/alias recursion regression passes in an isolated
  mdtest process;
- the owned-string example verifies normally;
- a 10 ms diagnostic owned-string profile completes without source-mapping
  errors;
- the default-threshold 15-second corpus profile reports no completed slow
  simple tactics and no verification failures.

There is no presently reproduced expansion or profiler-coordinate correctness
failure.

General condition solving now detects re-entry of the same condition query.
Without that guard, order facts over memory-loaded indices could cycle through
memory-load equality, pointer alias reasoning, and back into the original
order query until Rust aborted with a stack overflow. Re-entry returns
conservative "not decided"; it does not add a larger stack or hide the cycle
behind a timeout.

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
  (`vector_get.contract`, final `simp`): expanded and committed;
- the former `vector_fill.loop(0).preserve` `simp`: expanded to
  `close_invariants()` and committed;
- the former `vector_fill.contract` `execute_rest`: expanded to explicit
  statement and loop-summary certificates and committed;
- `examples/owned-string/owned_string.click:471:5`
  (`owned_string_pop.contract`, smart `have`): about 5.6 seconds;
- `examples/input-cursor/input_cursor.click:125:5`
  (`input_cursor_take.contract`, `simp`): about 3.8 seconds.

The final `vector_fill` smart `simp` has now been expanded. Grouped capture
records each claim transition separately, loop-summary invariant outputs retain
their exact source provenance, and pure certificate replay resolves listed
premises through that certified mapping instead of re-lowering them against an
ambient context.

`vector_push_first` now verifies, including its final `simp`, and its remaining
slow `execute_step` at `examples/owned-vector/vector.click:387:5` expands
successfully. The failure attributed to the final `simp` was stale: later
certificate construction had exposed three representation bugs in the caller.
Equality chains now compare pointer loads through their canonical observable
memory, certified structural assertions are not re-executed after their proof
has already established them, and theorem requirements canonicalize direct
memory loads so unrelated local materialization is not part of a source-level
value's identity. Historical comparison synthesis also uses every recorded
state with the required memory snapshot, and a statement's selected certified
fact transports are owned by that statement transition rather than replayed
again afterward.

A 120-second owned-vector profile reaches `vector_pipeline`, so there is no
remaining `vector_push_first` correctness failure. It reports:

- a 22.1 second smart `execute_until` at
  `examples/owned-vector/vector.click:459:5`;
- a 2.9 second smart `execute_step` at
  `examples/owned-vector/vector.click:387:5`;
- a project timeout while the smart `execute_until` at
  `examples/owned-vector/vector.click:478:5` was active.

The former 674 ms simple `assumption` at
`examples/owned-vector/vector.click:290:5` is fixed. Post-execution
`assumption` now resolves an unchanged ensure proposition through the checked
surface-to-kernel mapping established by the preceding certified `have`,
instead of re-lowering the quantified goal from the full ambient fact set. The
same location is now below the profiler's 1 ms reporting threshold, and a
fresh default-threshold profile reports no completed slow simple tactics.

`bubble_pass3_max_suffix.md` now passes. Loop initialization plans against the
authoritative lowered invariant goal when duplicate surface lowering is not
possible, branch-condition spellings survive certified fact transports, and
conditional universal order facts can participate in a transitive proof even
when the instantiated variable has the same internal id as the quantifier
binder.

`bubble_sort3_two_pass_sorted.md` now passes. Forward execution-proof traversal
retains the exact surface spellings and program-point snapshots exported by
loops, predicate unfolding preserves the source-site scope of historical
array reads, and quantified replay handles alpha-renamed binders without
ambient search. The kernel order graph can also finish a symbolic bound chain
through an intrinsic signed-constant comparison, which certifies the snapshot
loadability used by this example.

The focused bubble-sort regressions pass; a full mdtest sweep has not yet been
rerun, so the next corpus frontier is not currently known.

This sweep fixed two expander correctness bugs. Grouped expansion now preserves
one closer per claim even when multiple claims end in structurally identical
tactics. Source printing now recursively uses Click syntax inside quantified
and range propositions, and premise-free certified derivations print as
`normalize()` backed by context-free derivation replay.

The former 528 ms `apply_loop_summary` replay was a simple-tactic boundary
violation: after applying the verified loop rule, replay re-lowered every
invariant with the general point-proposition lowering machinery and silently
ignored failures. `apply_loop_summary` now does only its certified transition;
it does not eagerly manufacture proposition-map entries for possible future
tactics. Later explicit tactics lower and check their own premises at their own
program points. There is no search or ignored-error path.

Owned-string still times out at
`examples/owned-string/owned_string.click:485:5`, a final smart `simp` that
takes about 12 seconds in a focused 30-second profile.

The motivating `owned_string_set` successor proof at line 183 is fixed:
planning fell from 63.9 seconds to about 67 ms, and expansion emits a
one-premise arithmetic certificate.

## Next work

Work one frontier at a time and commit each logical change independently.

1. Expand the known-working `vector_pipeline` line 459 and
   `vector_push_first` line 387 certificates one at a time, reprofile, and
   inspect the line 478 frontier.
2. Continue the same cycle for
   owned-string line 485, owned-string line 471, and input-cursor line 125.
3. Run the full `click-audit` corpus audit and fix each concrete failure before
   claiming expansion is complete. The audit command now inventories every
   smart source site and independently expands and verifies it in bounded
   child processes; the complete three-site `jsonc-refcount` audit passes.
   Its next bounded trial found that `owned-segmented-buffer` currently fails
   original verification before inventory:
   `owned_segmented_buffer_pipeline.contract` tactic 22 is missing the exact
   `loadable(owner[0..1])` premise required by `step using`. Diagnose that as
   an example/verifier correctness issue before auditing its expansions.

Do not optimize by adding proposition-specific smart fast paths, broad ambient
premises, generic transport fallbacks, or internal-only certificate tactics.
