# `click audit` command

`click audit` inventories source-addressable smart tactics, expands selected
sites, verifies each rewritten proof unit, and checks that expansion reaches a
fixed point without introducing a new smart tactic.

## Synopsis

```text
usage: click audit [OPTIONS] <sidecar.click|example-project|examples-directory|mdtest.md|mdtests-directory|repository-root>
```

## Target selection

`TARGET` can be a sidecar, example project, examples directory, mdtest,
mdtests directory, or repository root. A repository-root audit covers both
`examples/` and `mdtests/`. `--claim`, `--changed-since`, and `--start-at`
narrow that target; their exact interaction and defaults are listed below.

## Checks

For each selected site, audit:

1. expands the source site;
2. verifies the rewritten proof unit in the retained session;
3. reverifies it through the ordinary targeted verification entry point;
4. confirms that the claim's smart-site multiset strictly shrinks and that no
   new smart tactic appears;
5. re-expands to confirm the fixed point;
6. on the first site in a claim, compares cold original and rewritten
   verification.

A cold performance regression fails only when the rewritten proof is both more
than twice as slow and beyond the configured slack, and the comparison repeats
in a second serial run. Raw time growth by itself is not a size-independent
failure.

## Options and defaults

| Option | Default | Meaning |
| --- | ---: | --- |
| `--session-time-limit DURATION` | `5m` | Limit original-sidecar session initialization. |
| `--discovery-time-limit DURATION` | `5m` | Compatibility alias for `--session-time-limit`. |
| `--expansion-time-limit DURATION` | `2m` | Limit one source expansion. |
| `--verification-time-limit DURATION` | `5m` | Limit rewritten-sidecar verification. |
| `--performance-slack DURATION` | `500ms` | Set the minimum same-run rewritten regression. |
| `--slow-site-limit DURATION` | `500ms` | Deprecated alias for `--performance-slack`. |
| `--time-limit DURATION` | `10m` | Limit the whole audit and print a resume cursor on exhaustion. |
| `--start-at PATH:LINE:COLUMN` | none | Resume inclusively at a source location. |
| `--claim CLAIM` | all | Select an exact claim. Repeat the option to select several claims. |
| `--changed-since REVISION` | none | Select claims affected since a Git revision. |
| `--verbose` | off | Print one success row per smart site instead of one per claim. |
| `--keep-going` | off | Continue after failures instead of stopping at the first failure. |
| `--max-sites COUNT` | unlimited | Run a positive bounded number of sites and print the next cursor. |
| `-h`, `--help` | none | Print command help and exit successfully. |

Duplicate claim selection, a zero site count, an unknown claim, and an
ambiguous claim across sidecars are errors.

## Output and exit behavior

Passing progress is one row per claim unless `--verbose` is set. A bounded or
timed-out run prints a resumable `--start-at` command with the active selection
and output mode. The summary distinguishes passing sites, site failures, and
incomplete work.

The command exits with status 1 for any audit failure or exhausted hard limit.
A full audit is a manual release and certificate-boundary gate, not part of
ordinary `scripts/check.sh`.

## Example

Audit all examples and mdtests, continuing long enough to collect independent
failures:

```sh
click audit --keep-going .
```

## Related commands

Use [`click verify`](verify.md) for ordinary correctness and
[`click profile`](profile.md) for performance diagnosis. The
[auditing concept](../../concepts/audit.md) explains how audit extends the
checks performed by [`click expand`](expand.md).
