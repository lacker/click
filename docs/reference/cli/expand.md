# `click expand` command

`click expand` replaces selected smart proof source with the checked operations
attributed to that success, rendered as an explicit Surface Click proof. It
verifies the complete rewritten source through the ordinary verification entry
point before emitting it. Expansion is an optimization and audit operation on
a correct proof; it is not a proof-repair command.

The rewrite removes avoidable planning and search while retaining the
unavoidable cost of parsing and directly checking the selected operations. A
smart hotspot should become approximately as cheap as that explicit checked
proof permits. A slow emitted simple operation is a verifier defect rather than
another expansion candidate.

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
complete rewritten proof unit before any output is written. Imported theorem
statements and unselected called-function contracts remain interface
assumptions; their proof bodies are not executed. Only the selected entry
module is rewritten, and imported source text is preserved byte for byte.

Generic theorem bodies are checked with rigid arbitrary type parameters.
Their proofs can be expanded and rechecked without a concrete client or a
selected type instance; expansion preserves the generic declaration.

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

## Output location and source context

A sidecar's `verifying "..."` declarations and its adjacent import manifest
resolve relative to the sidecar's own directory, so the emitted artifact must
stay verifiable at its output path:

- Writing into the source directory (`--output` there or `--in-place`)
  preserves the artifact byte for byte apart from the rewrite itself.
- Writing to another directory rebases every relative `verifying` declaration
  so it selects the same C file from the output location — for example
  `verifying "identity.c"` becomes `verifying "../source/identity.c"` — and
  re-verifies the rebased artifact through the output path's own loading
  rules. The requested path stays unwritten when that verification fails, and
  a destination whose adjacent import manifest would hijack the artifact is
  refused.
- A sidecar with an adjacent import manifest is anchored there: its manifest,
  roots, and locked artifacts resolve beside the sidecar by filename, so an
  `--output` that would move or rename it is refused before anything is
  written. Use `--in-place` for those sidecars.
- An mdtest expansion writes the whole `.md` file, whose C input fences live
  in the file itself, so no rebasing applies.

The rebasing never changes C sources or other sidecar text: only `verifying`
path literals move, so unselected source text is preserved.

## Output and exit behavior

Without an output option, the command writes the complete rewritten source to
standard output. An empty expansion deletes the selected tactic because the
smart success contributed no surface-expressible steps. A tactic written inside
a `branch` arm whose C path verification proved infeasible expands the same
way: the arm never runs, so the rewrite removes the tactic rather than
reporting a missing source occurrence.

The command exits with status 1 and writes no requested artifact when
selection, expansion extraction, rewritten proof verification, the
deadline, or file output fails. In-place output uses an adjacent temporary file
and an atomic rename after all checks pass.

A claim expansion whose explicit proof would nest `match`, `branch`, and proof
`if` regions past the checked drivers' bound of eleven is refused before it is
rewritten, with the diagnostic verification gives such a proof: move an inner
region into a contracted helper, or prove part of it in a `have`.

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
explains why the rewrite is trusted only after ordinary verification of the
rewritten source.
