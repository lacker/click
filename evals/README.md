# Evals

An eval scores Click on a fixed corpus and is compared across changes. None
of them runs in the gate: each takes from minutes to about an hour. A change
that an eval exists for quotes its result, before and after, in the pull
request.

| Eval | Measures | Run |
|---|---|---|
| `speed.sh` | Click's headline speed: nonblank `.click` lines verified per CPU second over a small fixed set of examples. `--work` adds deterministic work units per line, which compare across machines. | `evals/speed.sh [--work] [--runs N]` |
| `speed-survey.sh` | The same rate over every example, by wall time. Its number moves whenever an example is added or changed, so it is a survey, not the headline. | `evals/speed-survey.sh` |
| `auto.py` | How many hand-written `have` statements in the examples `auto` proves where they stand, and how many can be deleted outright, each compared with the committed baseline. | `evals/auto.py [--jobs N] [--only PATH]` |

`docs/internals/testing.md` describes the speed evals ("The key benchmark").

## The `auto` eval

Proofs are long because they spell out facts and proofs the automation could
find on its own. Each `have` in the corpus is a site, measured twice in a
scratch copy of the project, verifying only the proof unit that contained
it; `examples/` is never modified.

- `by_auto`: the `have`'s justification is replaced by `by auto;`. This
  measures `auto` itself: a site that holds is a hand-written proof `auto`
  can replace.
- `deletable`: the whole statement is deleted. A site that holds is a fact
  the automation finds and no later step cites by name, so the proof gets
  that much shorter. A fact `auto` proves can still be needed: a later
  `rewrite(...)` names it.

The verdict is the exit status; a failure's label (`budget`, `timeout`,
`syntax`, or `failed`) is read from the diagnostic for convenience only.

- `auto/corpus.txt` lists the projects. Each sidecar contributes at most
  `--per-file` sites (default 20), sampled with a fixed seed so every run
  measures the same sites.
- `auto/baseline.json` records, for each site, both verdicts. A
  site is keyed by its file, its written proposition and which occurrence of
  that proposition it is, so edits elsewhere in a file do not move it.
- A change to `auto`, `simp` or what they rely on runs the eval and quotes
  the summary: sites gained and lost under each measure, and why each lost
  site is acceptable.
  When the change is accepted, `--write-baseline` updates the baseline in
  the same pull request.
- A sidecar that does not verify unmodified is reported as skipped; it is
  not counted.

Each site is edited alone. Two deletable `have`s are not always deletable
together, so shortening a proof still means editing and re-verifying; the
eval says where to look and whether a change helped.
