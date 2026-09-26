# Finite paths through a two-successor graph

`walk_frame` relates two graph snapshots by equality of their successor cells
inside `0..n`. Bounded successors keep every recursive step in that range.
Logical reads are total, so this pure theorem needs no memory permission or
implicit validity premises. Both directions of branching are checked.
`closed_marks_exclude_target` proves path exclusion by structural induction;
`exhausted_zero_entry` derives its closed marked set from the recursive failure
summary, unchanged target cell, and all-unmarked entry condition.

Their proof bodies live in `branching_graph_paths.click`, which the mdtest
gate checks as an entry module; `branching_graph_dfs.md` imports the same
declarations.

```click
import "branching_graph_paths.click";
```

```expect
pass
```
