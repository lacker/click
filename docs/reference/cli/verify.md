# `click verify` command

`click verify` checks a complete sidecar, one selected proof unit, or every
sidecar in a project collection. Use it before profiling or expansion.

## Synopsis

```text
usage: click verify [--time-limit <DURATION>] <sidecar.click>[:<line>:<column>]
       click verify --trace-proof <FUNCTION> <sidecar.click>
       click verify [--time-limit <DURATION>] <project-directory|examples-directory>
       click verify --changed-since <REVISION> [--explain] <sidecar.click|directory>
```

Replace the following:

- `DURATION`: a duration such as `500ms`, `30s`, or `2m`.
- `SIDECAR`: the path to a `.click` sidecar.
- `LINE` and `COLUMN`: one-based coordinates inside a proof unit.
- `PROJECT_DIRECTORY`: either one project containing sidecars or a directory
  whose immediate subdirectories contain projects.
- `REVISION`: a Git revision used as the incremental baseline.

## Target selection

A sidecar target verifies every proof owned by that sidecar. A
`PATH:LINE:COLUMN` target verifies only the proof unit containing that
location. Imported declarations are available, but importing does not select
their proof bodies; similarly, an unselected called C function contributes its
well-formed contract without recursively selecting its implementation proof.
The retained proof artifact records this selected/assumed boundary.

For a directory, Click first treats the directory itself as a project when it
contains sidecars. Otherwise, it discovers projects in immediate
subdirectories. It prints one progress line per verified sidecar and a final
sidecar and project count.

## Options

| Option | Meaning |
| --- | --- |
| `--time-limit DURATION` | Set the outer deadline independently for each selected sidecar or proof unit. The default is `30s`. |
| `--trace-proof FUNCTION` | Verify only this C function in one sidecar and, on a proof error, show checked steps on its failing path with added facts and changed resource counts. Trace output is bounded. |
| `--changed-since REVISION` | Select claims affected since a Git revision. Reuse requires a valid full-verification marker for the baseline and verifier binary. |
| `--explain` | With `--changed-since`, print the incremental selection without verifying it. |
| `--allow-sorry` | Dev-only debugging switch: admit proof units whose body is exactly `sorry();` without checking them. Admissions are reported loudly, never recorded in incremental baselines, and `click audit`, `click expand`, and `scripts/check.sh` never enable the flag. Cannot be combined with `--changed-since`. |
| `-h`, `--help` | Print command help and exit successfully. |
| `--` | Stop option parsing; the remaining argument is the target path. |

`--explain` without `--changed-since` is an error. A missing or invalid
baseline marker forces a full rebuild rather than trusting an unattested
result. A marker records the C target, the verifier binary, the commit, the sidecar, and
every `CLICK_*` environment variable that was set, so a baseline attested
with a switch such as `CLICK_DISABLE_TACTIC_BUDGETS` is not reused by a run
without it. A full rebuild attests `HEAD`, and also the requested baseline
only when the commit's sidecar, declared C sources, and transitively included
local headers exactly match the inputs that were verified. An uncommitted
header change cannot attest the original commit. Files changed after
verification do not change which input snapshot the marker records.

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
[Supported C0](../language/c0.md#selecting-a-target), and that selection also
separates incremental verification markers.

Successful file or location verification prints one `external assumptions:`
line for each verified function whose transitive C call closure uses an
external contract, for example `external assumptions: probe -> strlen`.
Directory verification also prints these lines alongside its progress.
Incremental explanation prints selected and reused functions with the reason
for any full rebuild; an incremental verification prints the same assumption
lines for the claims it actually verifies.

The command exits with status 1 when parsing, source loading, target discovery,
verification, or the outer deadline fails. A proof failure is a correctness
result; repair it before using `click profile` unless unexpected slowness is
itself the failure being investigated.

When a proof error identifies a C function, the CLI suggests a rerun with
`--trace-proof` and fills in the function and sidecar path. The trace includes
successful simple steps before the failed attempt; the ordinary error starts
with the failed check, shows the Click goal and a source excerpt when its
written tactic can be located, and omits the internal premise dump. A trace reports
facts introduced into the focused proof context and changes to exact resource
representations. Retained Click goals and facts print in Click syntax. Generated
facts without an exact Click spelling are labeled internal and carry bounded
kernel detail, rather than being presented as source expressions. A surface
goal that reads memory also shows a separate internal snapshot identity, so
its read can be compared with an internal fact's read. The trace does not print
whole memory snapshots. It records up to
2,048 checked steps and renders at most 64 KiB. The trace option requires one
C sidecar file and cannot be combined with location or incremental selection,
or `--allow-sorry`. A trace run does not record a full verification baseline.

## Examples

Verify one sidecar:

```sh
click verify examples/input-cursor/input_cursor.click
```

Verify one project and then all example projects:

```sh
click verify examples/input-cursor
click verify examples
```

The rbtree examples make the full scope explicit: the model is selected as its
own theorem-only project, while the insert entry imports it without selecting
it a second time.

```sh
click verify examples/rbtree-model
click verify examples/rbtree-insert
```

Explain incremental selection from the previous commit:

```sh
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
