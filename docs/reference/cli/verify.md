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
| `--time-limit DURATION` | Set the outer deadline independently for each selected sidecar or proof unit. The default is 30 seconds. |
| `--changed-since REVISION` | Select claims affected since a Git revision. Reuse requires a valid full-verification marker for the baseline and verifier binary. |
| `--explain` | With `--changed-since`, print the incremental selection without verifying it. |
| `-h`, `--help` | Print command help and exit successfully. |
| `--` | Stop option parsing; the remaining argument is the target path. |

`--explain` without `--changed-since` is an error. A missing or invalid
baseline marker forces a full rebuild rather than trusting an unattested
result.

## Output and exit behavior

Successful file or location verification is silent unless the selected mode
has progress to report. Directory verification prints progress. Incremental
explanation prints selected and reused functions with the reason for any full
rebuild.

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
