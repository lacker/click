# `click verify` command

`click verify` checks a complete sidecar or mdtest, one selected proof unit,
or every sidecar in a project collection. Use it before profiling or
expansion.

For a compiler-backed proof, `click verify proof.click` checks the captures
for its `verifying` sources and refreshes missing or stale ones before
verification. A proof-only edit reuses the captures. `click verify --locked
proof.click` requires existing, current captures and runs without the
compiler. Use [`click capture`](capture.md) to refresh inputs explicitly.

## Synopsis

```text
usage: click verify [--checked-only] [--locked] [--work-limit <UNITS>] [--time-limit <DURATION>] <sidecar.click|mdtest.md>[:<line>:<column>]
       click verify [--checked-only] [--locked] --trace-proof <PROOF|PATH:LINE[:COLUMN]> [--trace-to <LINE[:COLUMN]>] <sidecar.click|mdtest.md>
       click verify [--checked-only] [--locked] [--work-limit <UNITS>] [--time-limit <DURATION>] <project-directory|examples-directory>
       click verify --changed-since <REVISION> [--explain] <sidecar.click|directory>
```

Replace the following:

- `DURATION`: a duration such as `500ms`, `30s`, or `2m`.
- `UNITS`: a positive count of deterministic work units, such as `50000000`
  or `50_000_000`.
- `SIDECAR`: the path to a `.click` sidecar.
- `MDTEST`: the path to a `.md` markdown test.
- `LINE` and `COLUMN`: one-based coordinates inside a proof unit.
- `PROJECT_DIRECTORY`: a directory; every sidecar under it is selected.
- `REVISION`: a Git revision used as the incremental baseline.

## Target selection

A sidecar target verifies every proof owned by that sidecar. Its imports
resolve within its project: the nearest directory at or above the sidecar
holding a `click.project.json`, or the sidecar's own directory when none does
([imports](../../concepts/sidecars.md#local-specification-imports)). A directory target
verifies every sidecar under it, at any depth, grouped by the project each
belongs to; hidden directories and `target` are skipped, and a project's
declaration modules are not entries. A `PATH:LINE:COLUMN` target verifies only the proof
unit containing that location. Imported declarations are available, but importing does not select
their proof bodies; similarly, an unselected called C function contributes its
well-formed contract without recursively selecting its implementation proof.
The retained proof artifact records this selected/assumed boundary.

An mdtest target verifies the Click block and the C or C++ fences embedded in
one markdown test, extracted and prepared exactly as the mdtest gate,
[`click profile`](profile.md), [`click expand`](expand.md), and
[`click audit`](audit.md) extract them. Its Click imports resolve beside the
markdown file, and `LINE` and reported source excerpts refer to lines of the
`.md` file. `click verify` reports the proof outcome itself and does not
consult the ```` ```expect ```` block, so an mdtest that expects a failure
exits nonzero; the mdtest gate is what compares an outcome with its
expectation. `--changed-since` does not take an mdtest.

For a directory, Click first treats the directory itself as a project when it
contains sidecars. Otherwise, it discovers projects in immediate
subdirectories. It prints one progress line per verified sidecar and a final
sidecar and project count.

A project's entries are its `.click` files except its declaration modules. A
declaration module declares only imports, specification types, predicates,
pure functions, and resources: no `verifying` or `target` source, no
`runtime`, no theorem, no named contract, and no C function proof. It owns no
claim, and the struct layouts its resources name come from an importer's
`verifying` sources, so it is checked where a sidecar imports it and is not
verified on its own. A file with a theorem or any other claim is an entry
even when others import it, because importing assumes its theorem statements
rather than checking their proofs.

## Options

| Option | Meaning |
| --- | --- |
| `--checked-only` | Replay with proof search disabled. Write the execution steps and obligation proofs explicitly. Requires full or location-selected verification without `--allow-sorry` or `--changed-since`. |
| `--locked` | Require existing, current captures and skip compiler invocation. |
| `--work-limit UNITS` | Set the deterministic whole-run work budget independently for each selected sidecar, mdtest, or proof unit. The default is `50000000`. |
| `--time-limit DURATION` | Set the wall-clock crash-containment bound independently for each selected sidecar, mdtest, or proof unit. The default is `10m`. This is not a verdict about the proof; see [Deterministic verdicts](#deterministic-verdicts). |
| `--trace-proof PROOF` | Verify only this C function, theorem, or user-defined tactic of one sidecar, selected by name (a Rust item by its path or, for an operator-trait method, its qualified form such as `<adler2::algo::U32X4 as MulAssign<u32>>::mul_assign`), or by `PATH:LINE[:COLUMN]` of the target, which selects the function, theorem, or tactic owning the claim whose clause or proof covers that line ([claim labels](expand.md#claim-labels)), and, on a verification refusal, show checked steps on its failing path with added facts and changed resource counts. A sidecar cannot declare one name as both a C function and a theorem, so the name alone selects the proof. Other tactic contracts stay assumptions when tracing a tactic. Theorems that the traced theorem cites stay assumptions, and no C function is verified for a theorem trace. If the script completes but contract certification fails, show the failed obligation and a bounded view of facts available to that check. Trace length and total output size are not capped; individual fact previews remain bounded. |
| `--trace-to LINE[:COLUMN]` | Focus `--trace-proof` on a written tactic at this source location, including in a successful proof; the tactic may sit inside a proof `match` arm, an arm of a proof `if`, `cases` or `all`, or a loop's `maintain` body, whose trace is shown under the enclosing proof's path up to the `loop`. A target after a proof `if` or `cases` whose arms both check it is traced through the first arm. Without it, the trace follows the failing tactic. |
| `--changed-since REVISION` | Select claims affected since a Git revision. Reuse requires a valid full-verification marker for the baseline and verifier binary. |
| `--explain` | With `--changed-since`, print the incremental selection without verifying it. |
| `--allow-sorry` | Dev-only debugging switch: admit proof units whose body is exactly `sorry();` without checking them. Admissions are reported loudly, never recorded in incremental baselines, and `click audit`, `click expand`, and `scripts/check.sh` never enable the flag. Cannot be combined with `--changed-since`. |
| `-h`, `--help` | Print command help and exit successfully. |
| `--` | Stop option parsing; the remaining argument is the target path. |

To replay a single expanded claim, give its source location as
`click verify --checked-only proof.click:LINE:COLUMN`. Whole-file
checked-only verification also checks the program termination proof
explicitly. Generate that proof with `click expand --claim program.termination`.

A C parsing stop at the whole-run work budget reports `work limit reached`.
The report identifies the budget and parsing phase. Audit reports use the
same error kind.

A `close()` that exhausts its own work budget reports `unsuccessful search` and
retains its already-checked prefix, including
accepted steps inside nested `have` blocks and loop bodies. An unfinished
claim contributes no accepted fact to that trace.

`--explain` without `--changed-since` is an error. A missing or invalid
baseline marker forces a full rebuild rather than trusting an unattested
result. A marker records the C target, the verifier binary, the commit, the sidecar, and
every `CLICK_*` environment variable that was set, so a baseline attested
with a switch such as `CLICK_DISABLE_TACTIC_BUDGETS` is not reused by a run
without it. A full rebuild attests `HEAD`, and also the requested baseline
only when the commit's sidecar, declared C sources, and transitively included
local headers exactly match the inputs that were verified. An uncommitted
header change cannot attest the original commit. Files changed after
verification do not change which input state the marker records.

For a sidecar with Click imports, `--changed-since` currently uses the safe
fallback: it rebuilds the selected entry scope whenever it runs and does not
record a reusable incremental marker. Imported inputs are included in ordinary
proof artifact identities. This conservative fallback never executes imported
proof bodies merely because their declarations changed.

A full rebuild checks theorem-only sidecars too, even though their selected
C function count is zero. Once a baseline is attested, unchanged theorem-only
sidecars can be reused; changing their theorem definitions requires a full
rebuild. The same comparison lets a subsequent `--changed-since` run reuse
an explicitly requested baseline whose complete inputs matched the full
verification.

## Output and exit behavior

The command does not print the default C implementation target on every run.
Successful verification is relative to the target the sidecar selected, not a
portability claim. There is no target-selection flag: a sidecar selects its
target with the `target` directive described in
[Supported C](../language/c.md#selecting-a-target), and that selection also
separates incremental verification markers.

Successful file or location verification reports every
[library interface](../../concepts/trust.md#library-interfaces) the result relied on
in one place: one `assumptions:` line for each verified function whose
transitive call closure uses one, listing the models by family:

```text
assumptions: every function -> runtime: modeled-pthread v11: pthread create/join, ...
assumptions: probe -> extern: helper; C library: strlen; allocator: free, malloc; snprintf: "%u"
```

The families and their tags are `extern` (a sidecar's own `extern`
contract), `C library`, `allocator`, `snprintf` (by format), `C++ std`,
`Rust core`, `primitive` and `runtime`. The thread runtime is assumed by the
whole verification, so it is one `every function` line, printed first, when
the sidecar selects one. The other families come from the same call closure
targeted verification computes; a C++ or Rust function's closure follows the
calls of its imported body, and imported names are printed as their source
language writes them (`slice::len<u8>`). Directory verification also prints
these lines alongside its progress.

An external assumption is one about a function the project does not verify.
Before a project directory's sidecars are verified, the command reads every
sidecar's sources and refuses the directory, naming the declaration and both
sidecars, when one sidecar declares `extern` a function that a sibling
sidecar's `verifying` source defines. Each sidecar is verified on its own, so
nothing would compare the assumed contract with the verified one, and a call
into a sibling sidecar is not ranked for termination: two sidecars assuming
each other's contracts would otherwise certify two functions that never
return. This is the directory form of the single-sidecar rule that refuses an
`extern` declaration of a function one of its own `verifying` sources defines.
Verify the defining source in the declaring sidecar as well (`verifying
"callee.c" as callee;`), or put both in one sidecar.
Incremental explanation prints selected and reused functions with the reason
for any full rebuild; an incremental verification prints the same assumption
lines for the claims it actually verifies.

The command exits with status 1 when parsing, source loading, target discovery,
or verification fails, a work budget is exhausted, or the crash-containment
bound stops the run. A proof failure is a correctness
result; repair it before using `click profile` unless unexpected slowness is
itself the failure being investigated.

Verification reports use these headings:

| Heading | When Click uses it |
| --- | --- |
| `tactic error` | Click refused a written tactic or an implicit proof step. For example, `step()` found no statement left or lacked evidence that a store was in bounds. |
| `unsuccessful search` | A proof search ran and could not close a goal, for example a written `close()` or a statement’s implicit closer. |
| `incomplete proof` | The proof ended with a requirement outstanding, such as a resource the contract promises to return. |
| `contract error` | Click identified a rule it believes the written contract violates, such as a potentially overflowing resource endpoint or a proven overlap between owned entry resources or between an owned resource and an input view. |
| `unsupported` | Click detected a documented limitation with a path to supporting it. The diagnostic identifies the unsupported case. |
| `syntax error` | Input did not parse. |
| `type error` | The source did not pass checking of names or types. |
| `work limit reached` | The run hit its `--work-limit` before it finished checking. The report names the phase or tactic that was running when it stopped. |
| `timed out` | The wall-clock crash-containment bound stopped the run before it gave a verdict. |
| `internal error` | Click detected a verifier failure, including ordinary checking that exhausts an internal work allowance or refuses verification without assigning a diagnostic category. |

A tactic error at an implicit step names that operation in the report, even
without a proof trace. A direct refusal can name required evidence, such as
an initialized value for a read. An unsuccessful search reports the proof
obligation it tried to close.

When a verification refusal identifies a C function, theorem, or user-defined tactic that the sidecar
selects, the CLI suggests a rerun with `--trace-proof` and fills in the proof
name and sidecar path. The suggestion is printed only when that command is
accepted: `--trace-proof` resolves the name the same way. A traced sidecar that
fails to parse or check reports that error as an untraced run does. By default, the
trace follows the path to the failing tactic; `--trace-to` can select a written
tactic in a successful or failing proof. A checked proof `match` retains its
constructor facts and arm steps after certification; `--trace-to` can select
any live constructor arm. The ordinary error and the trace use
the same formatted failure report, including the written tactic and its source
location. A separate `To get a trace:` section gives the command to rerun.
The source excerpt points to the failing written tactic (including steps inside
`have` and `with`), and the ordinary error omits the internal premise dump.
When the report has a proposition to prove, it prints it on a `goal:` line: a
claim's remaining goal, or a refused C statement's requirement at the
statement's pre-state, such as a call precondition, the condition that rules
out a signed overflow, or a missing resource. A statement's goal is followed by
a `help:` line naming the explicit form that proves it; see
[Repairing a failed proof](../../concepts/tracing.md). Premises that are
verifier bookkeeping no proof can cite are counted rather than listed.
The ordinary error prints facts, goals, and rejected requirements in Click or
C syntax, with each constant in its checked type (`-56` for an `int32`,
`4294967240u32` for a `uint32`): a read of the entry memory is `old(...)`, a read at a recorded point
is `at(point, ...)`, and a read of any other memory is `at(<state A>, ...)`,
defined in a `where` list after the report (see
[proof-failure triage](../../concepts/proof-failure-triage.md)). In the trace,
`goal:` shows the checked proposition after rewrites and `adds:` uses that same
format for each admitted fact. The trace uses readable expressions only when
they preserve checked identities; its typed memory operands include their read
width, memory label (`state#N`), and address, with shared labels and a
construction legend.

A failed `normalize() using { ... }` that checks a recorded 64-bit read prints
`read-resolution check:` with the exact checked equality, the selected
producer's memory label, and the memory walk's stopping memory and reason. If it recovered a
complete word, the report prints that word's comparison with the requested value
and whether the current equality context established it. Otherwise it reports
that no complete word was recovered and that comparison was not attempted.
These are retained results of the check itself; formatting does not rerun the
resolver or guess which premise would make the proof succeed.

A rejected cited premise of `transport(source, target) using { ... }` prints
`required transport premise:` with that exact lowered proposition under the
same labels as the goal and retained checked prefix. This also applies to
fixed-state checks and loop-body execution; it does not replace the premise
with an abbreviated dump of available facts and resources.

A checked function-pointer load step prints the local it produces, the exact
value label, and `read: load_function_pointer(address) in state#N`, where
`state#N` is the memory label of the read, not a surface program point.
The diagnostic uses `at(point, expression)` only when it has a program point
that names the expression. The address and
value share labels with subsequent facts and goals; the legend distinguishes
concrete function addresses from symbolic function addresses. The read's memory
comes from the accepted statement evidence, including entry initialization and
resource preparation, rather than from the later proof state.

The trace also prints `admitted read equality:` for each new checked-read
input or pointer, scalar, or offset equality involving a producer-defined read
value retained in the step's egraph context. These use the same proposition
printer and labels as `adds:` and `goal:`. Query-only registrations and discarded
scratch contexts are excluded. Context replacement is identified explicitly;
equalities inherited from a common prefix are not printed again. A callback
load with no such input says `no checked read equalities admitted by this step`.
This reports actual admissions, rather than guessing a missing equality, and
reads the selected history delta without searching older facts.

Call memory origins list the recorded caller-owned ranges retained
beside the write footprint and their placement premises. Each list shows up to
128 entries and explicitly counts any omitted entries. Source text is not printed in place of a fact that depends on which memory it reads.
Fresh model-field values also keep distinct value labels: a field hint such as
`c.value` alone cannot distinguish its values before and after a call.
A call refused because a named resource argument does not match prints its
held and required resource facts with the shared typed resource formatter and
one value/memory legend. Pointer arguments retain their checked types, distinct
identities, and read memory labels, including unnamed components that have no C
form. The error identifies the rejected argument ordinal without guessing
which premise was missing.
Resource facts elsewhere use the proposition printer's source/typed display
policy. Resource arguments use the same value printer as proposition operands,
including model values and `at(...)`-qualified reads. A resource list shares one label table
and construction legend across its entries. Source place helpers retain field,
mutex-storage, and iterated-ownership forms.
A call refused at stable-view recovery prints each pending checked goal and
its recorded obligation context. Required call clauses also identify the
callee and source input clause when lowering retained that identity. These goals
use the same proposition printer and shared memory legend as facts and
ordinary proof goals; they are pending obligations, not established facts.
Return-fold certification refusals print the exact rejected path fact using
that same format. Their traces retain the available checked prefix and label
it as a certification failure, rather than an accepted path.
Call requirements use the same direct AND/OR rule as `close()`: every
conjunct must hold, and one known disjunct suffices. Atomic equalities use the
scoped equality graph. This checks the goal's structure and indexed evidence;
it does not unfold definitions or search for implication premises. An unknown
requirement remains a proof obligation.
A named-resource rewrite that introduces a fact outside its checked body reports
`rejected fact:` followed by the exact checked proposition, then the facts
allowed by that resource body. These facts use the shared proposition printer
and the report's memory legend. Up to twelve allowed facts are displayed;
any further entries are explicitly counted. This comparison is diagnostic
only and does not turn the rejected proposition into an assumption.
An `close()` failure on an existential goal suggests the
`witness(value)` tactic. A trace reports facts introduced into the
focused proof context and changes to exact resource representations, using
Click syntax where it represents the checked fact. It follows only the
branch relevant to the selected tactic and does not print whole memory
states. It retains the complete checked path and does not cap the total
number of steps or output bytes. Individual fact, resource, and label previews
remain bounded. Traces are collected and rendered in memory, so memory use
grows with the recorded trace. Redirect a long trace when useful:

```console
click verify --trace-proof my_proof entry.click > trace.txt 2>&1
```

A rejected `branch ensuring` or `match ensuring` interface names the written
fact and retains the failing arm's checked prefix and guard. This also covers
a branch with only one feasible arm.

The trace option requires one
C sidecar file and cannot be combined with location or incremental selection,
or `--allow-sorry`. A trace run does not record a full verification baseline.

A completed `loop` appears as a checked step, with every visible fact it
introduces to the continuation, including its exit disjunction. The loop's
exported fact list is not shortened by the ordinary per-step fact preview
limit; individual facts use the same bounded printer and memory legend.
`--trace-to` can select the completed loop itself.

An unfinished loop `maintain` also retains its checked path for tracing. A plain
trace follows the path named by the frontier report; `--trace-to` can select a
checked tactic on that path or on another completed or unfinished arm. If the
target has no recorded checked step on a retained path, the trace says so.

A theorem trace shows the same checked steps as a function trace. A theorem
with several `ensures` clauses has one accepted path for each; a plain trace
of a successful theorem shows the first, and `--trace-to` selects the clause
whose proof contains the location. An imported theorem is an assumption of
the importing sidecar, so trace it through the sidecar that declares it.

## Deterministic verdicts

Every verdict is deterministic: the same sources verify or fail the same way
on any machine under any load. Two budgets, both counted in deterministic
work units (the units `click profile` reports), decide:

- each tactic's per-class budget (simple, smart, control), which names the
  tactic, its class, and its units when exhausted; and
- the whole-run budget of `--work-limit`, which also counts driver,
  certification, and lowering work outside any tactic, and names what was
  running when exhausted.

`--time-limit` is only crash containment. It stops a genuinely hung,
nonpolling, or CPU-starved run through a CLI process watchdog as well as the
cooperative deadline. A watchdog stop exits with a containment message and no
proof verdict. Successful operations cancel their watchdog. Library
verification keeps cooperative limits and does not terminate its host process.
A run stopped by containment says it was stopped by the
crash-containment bound and that this is not a verdict about the proof. No
tactic has a wall-clock limit. Verifier work that is slow but charges few
units is a Click defect, not a slow proof: `click profile` shows it as a
step whose time is out of proportion to its units, and only the
crash-containment bound stops it. The per-class budgets and their calibration
are in [Testing](../../internals/testing.md#time-bounded-runs).

## Examples

Verify one sidecar:

```console
click verify examples/input-cursor/input_cursor.click
```

Verify one project and then all example projects:

```console
click verify examples/input-cursor
click verify examples
```

The rbtree examples make the full scope explicit: the model is selected as its
own theorem-only project, while the insert entry imports it without selecting
it a second time.

```console
click verify examples/rbtree/rbtree-model
click verify examples/rbtree/rbtree-insert
```

Explain incremental selection from the previous commit:

```console
click verify --changed-since HEAD~1 --explain examples
```

## Related commands

Use [`click profile`](profile.md) on a green target to measure work. After
[`click expand`](expand.md) rewrites a proof, run `click verify` on the exact
rewritten artifact.

## Dev-only proof hole

The `sorry` tactic closes a goal without checking it, so
a failure can be reduced to its minimal shape while the rest of a project is
still checked. It is admitted in exactly two positions: as a complete
contract proof body (`by { sorry(); }`, which skips the function like an
`extern` declaration), and as a complete `have` body
(`have P by { sorry(); }`, which assumes `P` and checks everything else).
Anywhere else it is rejected, so a `sorry` can never cover an unbounded
suffix. It parses only under `--allow-sorry`. Admissions are reported
loudly, are never recorded in incremental baselines, and are rejected by
`click audit`, `click expand`, the mdtest harness, and `scripts/check.sh`,
which never enable the flag. Never commit a `sorry`: it proves nothing.
