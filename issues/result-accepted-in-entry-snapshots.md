# `result` is accepted inside `old(...)` and `at(function.entry, ...)`

## Violated invariant

A snapshot expression must only name state that exists at that snapshot.
`result` is the function's return value and does not exist at function entry,
so `old(result)` and `at(function.entry, result == 5)` have no meaning. The
surface accepts both today and treats `result` as snapshot-invariant, so the
proposition silently means the same as the unlabelled one.

This is not unsound: the kernel treats `result` as a rigid value on the path
and every probe that tried to smuggle a false claim through the entry label
was refused. The cost is in the tooling: the expander's snapshot-transport
closure (`try_snapshot_transport_closure` in
`src/surface/proof/smart_closures.rs`) tries `at(function.entry, goal)` first
and therefore emits a misleading no-op transport from function entry, wrapped
in a `have` plus `assumption`, where a direct closer would do.

## Reproduction

```c
int h(int x) { x = 5; return x; }
```

with the sidecar contract `ensures old(result) == 5;` proved by
`execute(); simp();` verifies. So does
`have at(function.entry, result == 5) by { simp(); }` inside a proof of `h`.
Expanding the round trip in `mdtests/byte_representation_roundtrip.md` shows
the effect: every failure arm discharges the claim with
`transport(at(function.entry, result == 18 or result == -1), ...)`.

## Intended regression

The surface rejects `result` under `old(...)` and under any `at(<label>, ...)`
whose label precedes the return, with a diagnostic naming the snapshot and the
reason. The expander no longer offers an entry-labelled transport for a goal
that mentions `result`, and the expanded round trip's failure arms close the
claim directly. Two mdtests pin the rejections, and the round-trip expansion
fixture pins the absence of the entry transport.

## Acceptance criteria

- `old(result)` and `at(function.entry, result ...)` are refused at validation
  with an actionable message; existing fixtures that never used them are
  unaffected.
- Expanded proofs of functions with early-return arms do not contain
  entry-labelled transports of goals about `result`.
- `scripts/check.sh` passes. Delete this issue and its list entry when the
  rejection, the expander change, and their regressions land.
