# `click verify` command

`click verify` checks a complete sidecar, one selected proof unit, or every
sidecar in a project collection. Use it before profiling or expansion.

## Synopsis

```text
usage: click verify [--time-limit <DURATION>] <sidecar.click>[:<line>:<column>]
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

A sidecar target verifies every claim in that sidecar and the C files named by
its `verifying` declarations. A `PATH:LINE:COLUMN` target verifies only the
proof unit containing that location and the C functions it calls.

For a directory, Click first treats the directory itself as a project when it
contains sidecars. Otherwise, it discovers projects in immediate
subdirectories. It prints one progress line per verified sidecar and a final
sidecar and project count.

## Options

| Option | Meaning |
| --- | --- |
| `--time-limit DURATION` | Set the outer deadline independently for each selected sidecar or proof unit. The default is `30s`. |
| `--changed-since REVISION` | Select claims affected since a Git revision. Reuse requires a valid full-verification marker for the baseline and verifier binary. |
| `--explain` | With `--changed-since`, print the incremental selection without verifying it. |
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

A full rebuild checks theorem-only sidecars too, even though their selected
C function count is zero. Once a baseline is attested, unchanged theorem-only
sidecars can be reused; changing their theorem definitions requires a full
rebuild. The same comparison lets a subsequent `--changed-since` run reuse
an explicitly requested baseline whose complete inputs matched the full
verification.

## Output and exit behavior

The command first prints its concrete C implementation target:
`C target: x86_64-linux-kernel (LP64, 8-bit unsigned plain char)`.
Successful verification is relative to that profile, not a portability claim.
The profile is currently fixed; there is no target-selection flag.

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

Explain incremental selection from the previous commit:

```sh
click verify --changed-since HEAD~1 --explain examples
```

## Related commands

Use [`click profile`](profile.md) on a green target to measure work. After
[`click expand`](expand.md) rewrites a proof, run `click verify` on the exact
rewritten artifact.
