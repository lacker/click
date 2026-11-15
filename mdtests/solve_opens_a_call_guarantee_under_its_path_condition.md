# `solve` opens a call guarantee under its path condition

A callee's conditional guarantee reaches the caller as an implication,
`r == 0 implies cell[0] == 0 and cell[1] == at(before_probe, cell[0])`.
Inside the branch whose path condition is exactly that antecedent, `solve`
concludes the consequent by modus ponens: the checked `extract` rule's
indexed consequent lookup finds the implication and sees its antecedent
available, so no `extract` block is written and nothing is searched. The
goal names the `before_probe` state as written, so it is looked up as
written rather than re-read at the branch's own program point, where
`cell[0]` has changed. `branching_graph_dfs.md` opens quantified
consequents the same way. The negative companion,
`solve_does_not_open_a_call_guarantee_off_its_path.md`, asks for the same
consequent on the other branch, where the antecedent is not available.

```c filename=probe.c
int32 probe(int32 *cell) {
    if (cell[0] == 0) return 1;
    cell[1] = cell[0];
    cell[0] = 0;
    return 0;
}
```

```c filename=use_probe.c
int32 use_probe(int32 *cell) {
    int32 r;
    r = probe(cell);
    if (r == 0) {
        return cell[1];
    }
    return 0;
}
```

```click
verifying "probe.c";
verifying "use_probe.c";

int32 probe(int32 *cell) {
    owns cell[0..2];
    ensures result == 0 or result == 1;
    ensures result == 0 implies cell[0] == 0 and cell[1] == old(cell[0]);
}

int32 use_probe(int32 *cell) {
    owns cell[0..2];
    ensures result == 0 or result == old(cell[0]);
} by {
    step();
    mark before_probe;
    step();
    step();
    if c(r) == 0 {
        have cell[0] == 0 and cell[1] == at(before_probe, cell[0]);
        step_until(function.exit);
        solve();
    } else {
        step_until(function.exit);
        solve();
    }
}
```

```expect
pass
```
