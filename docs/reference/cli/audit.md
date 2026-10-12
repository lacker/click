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
For a sidecar with Click imports, the inventory contains only smart sites owned
by the selected entry module. Its imports resolve under the project root
`click verify` selects for it, so a sidecar that imports a sibling project's
model, as `examples/rbtree-insert` does, audits as it verifies. The retained session keeps imported interfaces
fixed while checking each rewritten local proof; audit the library path itself
to select library sites.

The inventory includes smart tactics inside ordinary `have` bodies, including
nested bodies and checked proof arms. A smart container owns its body: its
inner aliases count as one site. Audit and profile use the same source table
as location-based expansion.

## Checks

A wholly selected claim is expanded once, with all its smart sites together.
The rewritten claim must contain no smart tactics and pass retained and cold
verification, including the performance comparison. A failed whole-claim
expansion fails the audit.

A cursor, site cap, or changed-source selection can select part of a claim.
The selected sites are captured together in one verification and applied as
one rewrite. The audit checks that each emitted region contains only simple
tactics, then verifies the rewritten proof unit once in the retained session
and once through ordinary cold targeted verification. It compares that cold
work with the original claim. Unselected automation remains in the source.

Every audit check counts deterministic work units, the units the tactic
budgets are charged, so the same source reaches the same verdict on any
machine under any load. The performance comparison fails when the rewritten
proof's cold verification spends both more than twice the original's work and
more than the configured slack beyond it. Each phase also fails when it spends
more than its work budget. Wall-clock times are reported as information only.
A phase time limit is a crash-containment bound for a hung or starved run, and
the whole-run time limit stops at a resumable cursor. Verification inside each
phase keeps the per-tactic work budgets [`click verify`](verify.md#deterministic-verdicts) applies; no tactic has a wall-clock limit.

## Options and defaults

| Option | Default | Meaning |
| --- | ---: | --- |
| `--session-work-limit UNITS` | `100000000` | Budget each of smart-site inventory and original-sidecar session initialization. |
| `--expansion-work-limit UNITS` | `50000000` | Budget the deterministic work of one expansion or re-expansion. |
| `--verification-work-limit UNITS` | `50000000` | Budget the deterministic work of one retained or cold proof-unit verification. |
| `--performance-slack UNITS` | `10000` | Set the minimum expanded-over-original work increase that can fail. |
| `--slow-site-limit UNITS` | `10000` | Deprecated alias for `--performance-slack`. |
| `--session-time-limit DURATION` | `10m` | Contain a hung inventory or session initialization. |
| `--discovery-time-limit DURATION` | `10m` | Compatibility alias for `--session-time-limit`. |
| `--expansion-time-limit DURATION` | `10m` | Contain a hung expansion or re-expansion. |
| `--verification-time-limit DURATION` | `10m` | Contain a hung proof-unit verification. |
| `--time-limit DURATION` | `10m` | Limit the whole audit, including inventory; print a resume cursor when sites are known. |
| `--start-at PATH:LINE:COLUMN` | none | Resume inclusively at a source location. |
| `--claim CLAIM` | all | Select an exact claim by its [label](expand.md#claim-labels), or `PATH:LINE[:COLUMN]`: the claim whose clause or proof covers that line of an audited sidecar or mdtest (Markdown lines), as `click expand --claim` resolves it, except that a line of a loop phase written in a `loop` tactic selects the proof that writes the tactic, whose sites include the phase's. A label shared by several audited files is ambiguous; a location names one. Repeat the option to select several claims. |
| `--changed-since REVISION` | none | Select claims affected since a Git revision. |
| `--verbose` | off | Include phase costs for each claim batch. |
| `--keep-going` | off | Continue after failures instead of stopping at the first failure. |
| `--exclude PATH` | none | Leave out a proof container, or every one under a directory. Repeat the option for several. A path that matches nothing in the audited path is an error. |
| `--max-sites COUNT` | unlimited | Run a positive bounded number of sites and print the next cursor. |
| `-h`, `--help` | none | Print command help and exit successfully. |

Duplicate claim selection, a zero site count, an unknown claim, and an
ambiguous claim across sidecars are errors.

## Output and exit behavior

Passing progress is one row per claim; `--verbose` includes its phase costs. A bounded or
timed-out run prints a resumable `--start-at` command with the active selection
and output mode. The summary distinguishes passing sites, site failures, claim failures,
session failures, and incomplete work.

The command exits with status 1 for any audit failure or exhausted hard limit.
A full audit is a manual release gate for expansion integrity and performance,
not part of ordinary `scripts/check.sh`.

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
