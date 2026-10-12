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

An unnamed resource witness can be rendered as `result` when it is exactly
the checked return pointer. Expansion rechecks that this spelling denotes
the same premise, including inside address casts and snapshot expressions.

## Synopsis

```text
usage: click expand [--work-limit <UNITS>] [--time-limit <DURATION>] [--output <PATH> | --in-place] <sidecar.click|mdtest.md>:<line>[:<column>]
       click expand --claim <LABEL|PATH:LINE[:COLUMN]> [--work-limit <UNITS>] [--time-limit <DURATION>] [--output <PATH> | --in-place] <sidecar.click|mdtest.md>
```

Replace the following:

- `UNITS`: the whole command's deterministic work budget; the default is
  `50000000`.
- `DURATION`: the whole command's wall-clock crash-containment bound; the
  default is `10m`.
- `PATH`: a destination for the complete rewritten sidecar or mdtest.
- `LINE` and `COLUMN`: one-based coordinates selecting a smart tactic. The
  column may be omitted when the line starts exactly one smart tactic.
- `LABEL`: one function, pure-theorem, or loop-phase claim label whose smart
  tactics are all selected; see [Claim labels](#claim-labels).
  `--claim PATH:LINE[:COLUMN]` selects the innermost claim whose clause or
  proof covers that line of the target instead.

## Selection

The location form selects one smart tactic by where it is written, at any
nesting depth: in a proof `branch`, `if`, `cases`, or `match` arm, a call's
`outcomes` arm, a loop's `initialize` or `preserve` phase, or the body of a
`have`. Coordinates in an mdtest refer to the Markdown file, not to the
extracted Click block.

- `PATH:LINE:COLUMN` selects the innermost smart tactic whose source text
  contains that position, so any column inside the tactic works, not only its
  first character.
- `PATH:LINE` selects the one smart tactic that starts on that line. When the
  line starts several, the command fails and lists each candidate as a
  `PATH:LINE:COLUMN` location to rerun with.
- A location outside every smart tactic, such as a blank column or the brace
  that closes a non-smart `have`, fails with a diagnostic instead of selecting
  a neighbor.

The locations `click verify` prints are accepted as written: the `--> PATH:LINE:COLUMN`
line of a diagnostic, and the `LINE` of its `tactic@LINE` or
`tactic@LINE:COLUMN` heading, which carries a column exactly when its line
starts more than one tactic.

A smart tactic that owns its body is one site. The `simp` written in a smart
`have` (`have P by { simp(); }`) or anywhere inside a smart `both` or
`close_invariants by` bundle selects that enclosing tactic, and expansion
rewrites the whole site. A `have` whose body mixes several tactics is not a
site itself; each smart tactic written in its body is, and expanding one
rewrites exactly that tactic's source, leaving its neighbors as written. The
same holds for a smart tactic in a proof `if` or `cases` arm written inside a
`have` body, and inside the body of a `have` in a loop's `initialize` phase.

The claim form expands every smart tactic in one named claim and is
useful when aggregate smart work matters even though no individual site is
slow. The claim is named by its [label](#claim-labels), including in
compiler-prepared Rust sidecars, or by a location its clause or proof covers:
`--claim PATH:LINE` or `--claim PATH:LINE:COLUMN`, where `PATH` is the target
sidecar or mdtest (in Markdown coordinates for an mdtest). A claim covers its
source from the clause keyword (`ensures`, `owns`, `produces`, `exceptional
ensures`) through the end of its `by`, a loop phase's proof, or a function's
grouped proof; a clause without its own `by` that the grouped proof covers
selects that grouped proof, `f.contract`. A loop phase's proof written in a
`loop` tactic, from its `initialize` or `preserve` keyword through the end of
its `by`, is a claim inside the proof that writes it, and a location there
selects the phase, `f.loop(N).initialize` or `f.loop(N).preserve`, rather than
that proof. Without a column the line must touch exactly one claim, not
counting a claim around another one the line touches; otherwise the command
fails and lists each claim as a `PATH:LINE:COLUMN` location to rerun with. A
line that no claim covers fails with `no claim's clause or proof covers this
line`. Source-cursor and claim-label expansion use the same checked theorem
verification path.

A loop phase claim rewrites only that phase: its written `by` clause becomes
the phase's checked certificate, and a phase the `loop` tactic leaves to
automation is written out as an explicit `initialize by { ... }` or
`preserve by { ... }` at the end of the tactic's body. The rest of the proof is
left as written, and the proof that writes the `loop` tactic is verified with
the rewrite. A `loop` tactic does not write which C loop it proves; checked
execution binds it, so resolving a phase label or a phase location checks that
proof. When several `loop` tactics prove one C loop, for instance one in each
arm of a proof `if`, the label is ambiguous and the command lists the tactics;
select one by a line of its phase with `--claim PATH:LINE`. As for any claim,
a phase without smart tactics is rewritten as its checked certificate.

### Claim labels

Click names each proof obligation with a claim label. Diagnostics, `click
profile`, and `click audit` print it, and `click expand --claim` and `click
audit --claim` accept it. `click verify --trace-proof` takes the function or
theorem name before the dot.

| Label | Claim |
| --- | --- |
| `f.contract` | The grouped proof of function `f` (`{ ... } by { ... }`), which proves every clause without its own `by`; also a tactic's proof. |
| `f.name` | The clause the author named, `ensures name: P`. |
| `f.ensures_N` | The `N`th written `ensures` clause of `f`, counted from 0 among its `ensures` clauses only. |
| `f.exceptional_ensures_N` | The `N`th `exceptional ensures` clause. |
| `f.owns_N` | The return obligation of the `N`th `owns` clause: the function gives back what it was lent. |
| `f.produces_N` | The `N`th `produces` clause, counting those inside a contract `if`. |
| `f.loop(N).initialize`, `f.loop(N).preserve` | A loop phase's proof: the `initialize` or `preserve` proof, written or left to automation, of the `loop` tactic that proves C loop `N` of `f`, counting its loops from 0 in source order. |
| `f.body_safety` | The body-safety obligation of a contract that states no claim, as diagnostics name it. |

Each clause kind counts separately, so adding an `owns` clause does not
renumber the `ensures` clauses: in `owns p[0..1]; ensures p[0] == 1;` the
clauses are `f.owns_0` and `f.ensures_0`. Theorems are labelled the same way,
`T.ensures_0`, `T.owns_0`, or `T.name`. A clause that names an aggregate
resource is one claim however many members it covers. `consumes`, `views`,
`requires`, and `constructs` state no obligation of their own and have no
label.

A Rust item's label uses its path, `quad::walk.contract`; an operator-trait
method uses Rust's qualified form,
`<adler2::algo::U32X4 as MulAssign<u32>>::mul_assign.contract`. Both forms,
and the name the importer gives the item, are accepted
([Rust](../rust.md)).

Generated execution arms may retain logical proof operations after their last
C step, such as unfolding a predicate on the returned state. Their checked
entry and join still require the C path to finish; a logical operation cannot
replace a missing C transition. `mdtests/sort3_sorted.md` covers whole-claim
expansion with predicate unfolds after execution.

Selection never changes how tactics are numbered: `click profile`, `click
audit`, and tactic timing keep their flat per-claim source indices, and a
tactic inside a `have` body is addressed by its enclosing `have`'s index plus
its written position in each body, and, inside an `if` or `cases` arm there,
by which arm and its written position in that arm.

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
| `--claim LABEL` | Expand all smart tactics in one named claim, including one loop phase, instead of selecting a tactic by location. `--claim PATH:LINE[:COLUMN]` names the innermost claim whose clause or proof covers that line of the target. |
| `--work-limit UNITS` | Set the deterministic work budget of the whole command, generating the expansion and checking it. The default is `50000000`. |
| `--time-limit DURATION` | Set the wall-clock crash-containment bound of the whole command. The default is `10m`. It stops a hung or CPU-starved run and is not a verdict about the proof; smart search inside the expansion is bounded by its deterministic smart work budget, not by a clock. |
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
selection, expansion extraction, or rewritten proof verification fails, a
work budget is exhausted, the crash-containment bound stops the run, or file
output fails. In-place output uses an adjacent temporary file
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

Select the only smart tactic on a line:

```sh
click expand path/to/file.click:LINE
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
