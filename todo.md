# `click-profile` / `click-expand` / `click-audit` Handoff

Last updated: 2026-07-28

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

Historical pure facts use one source form for both expressions and complete
propositions. `at(point, expression)` snapshots a value;
`at(point, proposition)` snapshots every state-relative component of an atomic
or compound claim, including the memory and range expressions in
`loadable(...)`.

`ProofSite` is the shared identity used by verification, profiling, selection,
and rewriting. It covers function claims, theorem claims, loop phases, and
structural items.

### Surface-language boundary

Kernel Click is an internal typed Rust representation. It has no textual
syntax. Every `.click` file, diagnostic expression, profiler hint, and
`click-expand` result is Surface Click and must parse with the ordinary parser.

Canonical Surface Click uses:

- `owner->field` for one imported struct field;
- `(owner->pointer_field)[start..end]` for storage reached through a pointer
  field;
- `object(owner)` for the complete ABI-aligned struct object;
- `c(name)` when a C lexical binding must be distinguished from a contract
  binding.

`load_int32`, `load_uint8`, their pointer-valued variants, and `byte_offset`
remain documented low-level Surface Click escape hatches for addresses whose
C source provenance is unavailable. They are not Kernel Click concrete syntax.
The canonical renderer must prefer retained field/object provenance and must
never reconstruct surface text by pretty-printing kernel terms.

`ContractExpression::Field` and the surface component of `ContractSegment`
retain this provenance separately from their lowered semantic expression.
Substitution must update both representations. A certificate is not valid
surface output unless parsing it again preserves the same lowered meaning.

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
unit. Standalone `click-verify` also verifies the target's transitive C-call
dependencies. Unrelated function proofs are not executed.

`click-audit` now inventories smart sites syntactically before running any
proof, orders them deterministically by file and source position, and creates a
reusable verification session lazily for each file reached by the audit cursor.
`--start-at PATH:LINE:COLUMN` inclusively resumes at a failed site without
initializing earlier files. Failures and bounded `--max-sites` runs print the
exact continuation command; the default sweep stops at the first failure, while
`--keep-going` requests failure collection. For each rewrite the session checks
that the AST changed only inside the selected proof unit, removes that target's
own cached function rule, and reverifies the target against its retained
certified dependencies. Expansion and session verification have separate
watchdogs; every timed-out child is killed and reaped.

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

- 458 library tests are currently discovered. The complete serial run reaches
  the historically slow expansion regressions; all completed tests pass after
  fixing the newly exposed surface-roundtrip failures.
- 7 `click-profile` binary tests pass;
- 9 `click-audit` binary tests pass;
- `click-audit` inventories and parses all 249 current smart source sites with
  the ordinary Surface Click parser;
- focused regressions pass for `object(owner)`, chained field access, indexed
  pointer fields, unfolded composite certificate printing, shifted range
  lowering, bounded loop execution, symbolic loop effects, implication
  certification, and same-block pointer congruence;
- the five struct-heavy flagship sidecars contain no remaining `load_*`,
  `byte_offset(...)`, or raw struct-cell range spellings.

The C/contract name-identity issue found by the corpus audit is fixed.
`c(name)` now denotes the C lexical binding explicitly, while an unqualified
name continues to use the contract namespace. In particular, `result` is the
contract result and `c(result)` is a C local or parameter named `result`.
Generated surface certificates preserve this distinction, including beneath
`at(...)`, and a focused grouped-`simp` regression expands and reverifies the
collision.

The current bounded audit frontier is performance rather than parsing:
initializing the first input-cursor verification session exceeds a one-minute
diagnostic limit after all 249 sites have been inventoried. Do not classify
that timeout as an expansion correctness failure without profiling the
initialization path.

The grouped loadability boundary now lowers the complete source proposition at
an exact `function.entry` or recorded program point. It no longer constructs a
candidate by replacing only the memory term of a current proposition. Explicit
loadability transport re-derives its target from the exact source plus
certified execution effects; condition transport continues to use the
condition frame theorem. Symbolic subranges also use the direct element rule:
`split <= index < len` selects cell `index` from `[split..len]` without
byte-scaled search.

General condition solving now detects re-entry of the same condition query.
Without that guard, order facts over memory-loaded indices could cycle through
memory-load equality, pointer alias reasoning, and back into the original
order query until Rust aborted with a stack overflow. Re-entry returns
conservative "not decided"; it does not add a larger stack or hide the cycle
behind a timeout.

### Kernel theorem boundary

The theorem-minting boundary was redesigned on 2026-07-28:

- execution theorems retain all verification conditions as premises;
- caller-replayed outcomes are theorem-free candidates;
- path specifications must match the exact certified function, entry,
  arguments, and outcome;
- opaque contract evidence is bound to the complete annotated `CFunction`,
  not merely its name, signature, or source body;
- exact body-safety, ensure, resource-ensure, and effect claims are certified
  individually, and an opaque rule requires the complete claim set;
- the accepted contract frontier is kernel-private and derives assumptions
  only from the exact entry state and contract; proposed elaboration facts are
  admitted only when the kernel re-derives them;
- bounded concrete execution versus loop-rule verification is an explicit
  certificate mode, not a fallback;
- composite resource definitions and their logical facts are lowered into the
  kernel and checked during fold/unfold and claim certification;
- all execution obligations are discharged before even a body-safety claim can
  be certified.

Failure to reproduce a complete exact claim set simply leaves the function
without an opaque rule. There is no weaker packaging fallback.

Regression tests cover retained non-assumable conditions, mismatched symbolic
paths, same-body/different-contract substitution, incomplete claim sets, and
body-safety evidence with an unresolved verification condition.

## Remaining correctness work

### 1. Complete the global certificate audit

`click-audit` is now the generated audit over proof-bearing source constructs.
The remaining work is to run it across the full examples corpus and fix every
concrete failure.

Current sweep status:

- parser inventory: 249/249 sites discovered and parsed;
- prior retained-session sweeps remain useful historical evidence, but must
  not be described as a current full-corpus pass after changing the surface
  representation;
- the next full audit should start at
  `examples/input-cursor/input_cursor.click:8:9` with a realistic session
  budget, after profiling session initialization.

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
- `click-audit --start-at` cannot advance within a file when reusable-session
  initialization itself times out. Profile and fix that initialization path;
  increasing the budget is diagnostic, not a final performance solution.
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

The former timing-driven retained-session audit passed all 67 smart sites that
it observed in owned-string. Most selected-proof checks take milliseconds to a
few seconds. The former
roughly 75-second `owned_string_pipeline.contract` checks at lines 550 and 551
now take about 0.31 seconds. Their final `return observed` certificate had
mistakenly copied every ambient implication premise from the monotone execution
theorem into a generated `step using`, forcing the simple replay through a
large irrelevant search. Returning a local or literal is total, reads and
mutates no memory, and consumes no proposition assumptions, so its statement
certificate is now premise-free while the certified transition preserves the
unchanged facts. Arithmetic and memory-reading returns continue to retain their
actual safety premises. Grouped outcome `simp` replay also reuses its already
lowered kernel goal instead of lowering the same surface expression twice.

That timing-driven audit also passed all 37 observed owned-segmented-buffer
sites, all 33 observed owned-split-buffer sites, all 29 observed input-cursor
sites, and all three jsonc-refcount sites. The previously documented
segmented-buffer baseline failure was stale.

The parser-driven inventory added by `click-audit --start-at` is deliberately
stronger than the old timing inventory. Loop invariants are not independent
proof sites: their obligations belong to the loop initialization and
preservation proofs, and the audit no longer advertises their parser-internal
`auto` marker as expandable.

Owned-vector exposed a grouped-`simp` boundary bug. Its ambient precheck could
reject a postcondition that the generated source-site certificate proved,
leaving `vector_push_first.ensures_3` unproved. Grouped proposition transitions
are now accepted exactly when their generated certificate successfully
replays; a certificate failure is a proof failure rather than a non-fatal
expansion blocker. `vector_push_first` verifies in about 6.4 seconds and all
413 library tests pass.

Owned-vector baseline performance is no longer blocking the audit. The
line-398 `vector_push_first` grouped `simp` is replaced by its explicit
historical-loadability transport certificate. `vector_pipeline`'s setup
`execute_until` is expanded into a checked `step using`, and its formerly
unbounded final transition is split at statement 6. That call now replays from
the exact current length facts, followed by the fast remaining step. The
29.8-second result-snapshot `have` is replaced by a two-premise `derive`.

This sweep also fixed three tool/engine bugs exposed by those certificates.
Post-execution `have` and `transport` now replay in source order per outcome,
and smart transport independently replays its emitted `TacticCertificate`.
Expansion dependency discovery includes the endpoint statement executed by
`execute_until`, so an endpoint call cannot lose its verified callee rule.
Finally, `step using` no longer injects every historical certified effect into
its explicit context before resource normalization; those facts remain at
their original snapshots and are restored after the selected transition.

A fresh release profile verifies all of owned-vector in about 15 seconds and
reports no smart tactic over 2 seconds, no simple tactic over 500 ms, and no
slow control container. All 423 library tests pass.

The retained-session owned-vector audit is green across all 71 real smart
source sites. Each selected occurrence expanded and its rewritten proof unit
reverified. The audit exposed and fixed five independent correctness issues:

- declared resource argument types are now filled recursively inside
  `at(point, proposition)`, so historical `contains(...)` facts lower exactly
  like current ones;
- loop invariants are excluded from the smart-site inventory because their
  proofs are the loop initialize/preserve phases;
- loop initialization certificates close quantified goals under binder
  renaming and observationally equivalent materialized memory snapshots, using
  the same replay-equivalence rule as explicit `assumption()`;
- tactic source lookup now visits structural items in `statement(...)` blocks,
  not only `loop(...)` blocks;
- expansion dependency pruning includes the complete call graph used by the
  verifier's whole-function structural traversal.

The motivating `owned_string_set` successor proof at line 183 is fixed:
planning fell from 63.9 seconds to about 67 ms, and expansion emits a
one-premise arithmetic certificate.

## Next work

Work one frontier at a time and commit each logical change independently.

1. Continue the profiling/expansion cycle for
   owned-string line 485, owned-string line 471, and input-cursor line 125.
2. Run the full `click-audit` corpus audit and fix each concrete failure before
   claiming expansion is complete. The audit command now inventories every
   smart source site syntactically, then independently expands and verifies it
   against a retained certified environment; `--start-at` resumes inclusively
   without initializing earlier files. The complete three-site
   `jsonc-refcount` audit passes. The new syntactic inventory exposed 11
   previously unvisited sites across owned-string, owned-segmented-buffer,
   owned-split-buffer, and input-cursor; audit those before calling the
   projects fully green. Owned-vector's complete 71-site audit now passes.

Do not optimize by adding proposition-specific smart fast paths, broad ambient
premises, generic transport fallbacks, or internal-only certificate tactics.
