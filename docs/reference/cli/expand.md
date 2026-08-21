# `click expand` command

`click expand` replaces selected smart proof source with the Surface Click
certificate already constructed, printed, and independently replayed for that
success. Expansion is an optimization and audit operation on a correct proof;
it is not a proof-repair command.

## Synopsis

```text
usage: click expand [--time-limit <DURATION>] [--output <PATH> | --in-place] <sidecar.click|mdtest.md>:<line>:<column>
       click expand --claim <LABEL> [--time-limit <DURATION>] [--output <PATH> | --in-place] <sidecar.click|mdtest.md>
```

Replace the following:

- `DURATION`: the whole-command limit; the default is `1m` (60 seconds).
- `PATH`: a destination for the complete rewritten sidecar or mdtest.
- `LINE` and `COLUMN`: one-based coordinates selecting a smart tactic.
- `LABEL`: one function-claim label whose smart tactics are all selected.

## Selection

The location form selects one source-addressable smart tactic. Coordinates in
an mdtest refer to the Markdown file, not to the extracted Click block. The
claim form expands every smart tactic in one named function claim and is useful
when aggregate smart work matters even though no individual site is slow.

The selected proof unit must verify before rewriting. Click verifies the
complete rewritten proof unit and the transitive contracts it calls before any
output is written. Unselected source text is preserved byte for byte.

## Options

| Option | Meaning |
| --- | --- |
| `--claim LABEL` | Expand all smart tactics in one named claim instead of selecting a location. |
| `--time-limit DURATION` | Override the default `1m` whole-command limit. |
| `--output PATH` | Write the complete verified rewrite to a different path. |
| `--in-place` | Atomically replace the input only after verification succeeds. |
| `-h`, `--help` | Print command help and exit successfully. |
| `--` | Stop option parsing before the positional target. |

`--output` and `--in-place` are mutually exclusive. Repeating a single-use
option is an error.

## Output and exit behavior

Without an output option, the command writes the complete rewritten source to
standard output. An empty expansion deletes the selected tactic because the
smart success contributed no surface certificate steps.

The command exits with status 1 and writes no requested artifact when
selection, expansion, certificate replay, rewritten proof verification, the
deadline, or file output fails. In-place output uses an adjacent temporary file
and an atomic rename after all checks pass.

## Examples

Write one expansion to standard output:

```sh
click expand path/to/file.click:LINE:COLUMN
```

Expand one claim into a review file:

```sh
click expand --claim function.contract \
    --output /tmp/expanded.click path/to/file.click
```

## Related commands

Use a recommendation from [`click profile`](profile.md), then verify the exact
output with [`click verify`](verify.md). [`click audit`](audit.md) applies the
same boundary systematically. The [expansion concept](../../concepts/expansion.md)
explains why the rewrite is trusted only after replay.
