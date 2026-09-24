# `click profile` command

`click profile` verifies a target while collecting structured attribution for
frontend, environment, tactic, certification, verifier-core, and driver work.
Use it to classify unexpected slowness after the selected proof verifies.

## Synopsis

```text
usage: click profile [OPTIONS] <sidecar.click|example-project|examples-directory|mdtest.md|mdtests-directory>
```

## Target selection

`TARGET` can be a sidecar, example project, examples directory, mdtest, or
mdtests directory. An mdtest is loaded from its fenced C or C++ and Click blocks
with the same preparation used by the mdtest gate. C++ fences use the pinned
compiler importer. Profiling ignores quarantine so a
specific quarantined fixture can be diagnosed. Each selected project receives
its own deadline and report.

Sidecar, example-project, and examples-directory targets select sidecars
exactly as [`click verify`](verify.md#target-selection) does: a directory that
contains sidecars is one project, and otherwise each immediate subdirectory
with sidecars is a project. A project report covers all of its sidecars, and
local imports resolve within the same project root `click verify` uses. A
directory is an mdtests directory instead when it directly contains a markdown
test, even if it also holds `.click` modules those tests import.

For a sidecar with local Click imports, profiling loads the same transitive
module graph as verification but executes and attributes only proof units
owned by the selected entry. Profile the library file itself to measure its
proofs.

## Options and defaults

| Option | Default | Meaning |
| --- | ---: | --- |
| `--smart-threshold DURATION` | `2s` | Report a completed smart tactic in a verified proof as an expansion candidate. |
| `--simple-threshold DURATION` | `500ms` | Report a slow simple tactic as a verifier performance defect. |
| `--control-threshold DURATION` | `2s` | Report a slow control-tactic container and its nested work. |
| `--threshold DURATION` | none | Set all three tactic-class thresholds together. It cannot be combined with a class-specific threshold. |
| `--time-limit DURATION` | `30s` | Set the wall-clock limit for each project. |
| `--top COUNT` | `8` | Limit each function and claim attribution ranking to a positive number of rows. |
| `-h`, `--help` | none | Print command help and exit successfully. |
| `--` | none | Stop option parsing before the target path. |

## Report interpretation

The report reconciles measured work into named phases. `SIMPLE`, `SMART`, and
`CONTROL` are exclusive tactic times. `CERTIFICATION` and `VERIFIER CORE`
cover checked work outside those operations. `PROCESS/DRIVER` covers source I/O
and known driver overhead. `INTERRUPTED` is unfinished time after a deadline;
`UNATTRIBUTED` indicates inconsistent or unknown accounting rather than a
healthy miscellaneous bucket.

Function and claim rankings are two views of the same work and must not be
added together. A slow smart success may be expanded. A slow simple tactic is an
engine defect. A prompt bounded smart failure has no successful proof to expand;
decompose the proof unless the search missed its bound or produced a misleading
diagnostic.

Expansion removes the successful smart site's planning and search, not the
unavoidable parsing and semantic checking of its emitted proof. The expanded
proof should therefore approach the cost of direct simple checking; it is not a
way to hide a slow simple operation.

An incomplete or failing target never receives an expansion recommendation.
Profile a non-verifying target only when a timeout or unexpected slowness is
the problem being diagnosed.

## Output and exit behavior

The command prints one report per selected project. It exits with status 1 if
any project fails verification or if target loading, event classification, or
the project deadline fails. A timeout report is explicitly partial.

## Examples

Profile all example projects:

```sh
click profile examples
```

Profile one mdtest and show five attribution rows:

```sh
click profile --top 5 mdtests/bubble_sort3_two_pass_sorted.md
```

## Related commands

Start with [`click verify`](verify.md). Use the printed
[`click expand`](expand.md) command only for a completed smart tactic in a green
proof. The [profiling concept](../../concepts/profiling.md) explains the
workflow and attribution model.
