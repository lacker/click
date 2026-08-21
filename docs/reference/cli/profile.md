# `click profile` command

`click profile` verifies a target while collecting structured attribution for
frontend, environment, tactic, certification, verifier-core, and driver work.
Use it to classify unexpected slowness after the selected proof verifies.

## Synopsis

```text
usage: click profile [OPTIONS] <sidecar.click|example-project|examples-directory|mdtest.md|mdtests-directory>
```

`TARGET` can be a sidecar, example project, examples directory, mdtest, or
mdtests directory. An mdtest is loaded from its fenced C and Click blocks with
the same extraction used by the mdtest gate. Profiling ignores quarantine so a
specific quarantined fixture can be diagnosed.

## Options and defaults

| Option | Default | Meaning |
| --- | ---: | --- |
| `--smart-threshold DURATION` | `2s` | Report a completed smart tactic in a verified proof as an expansion candidate. |
| `--simple-threshold DURATION` | `500ms` | Report a slow simple tactic as a verifier performance defect. |
| `--control-threshold DURATION` | `2s` | Report a slow control-flow container and its nested work. |
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
added together. A slow smart success may be expanded. A slow simple step is an
engine defect. A prompt bounded smart failure has no certificate to expand;
decompose the proof unless the search missed its bound or produced a misleading
diagnostic.

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
