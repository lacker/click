# A load that may read an earlier store's cell continues in each case

`g[u] = 7` may or may not write `g[0]`, so the load `r = g[0]` after it has
two checked successors: `r == 7` when `u == 0`, and `r == old(g[0])`
otherwise. The load is not the last statement, so each case has to continue with
the rest of the block under its own assumption.

The implicit tail of `planned`'s omitted proof splits on the case condition
before the load and runs the remaining statements once per case. The explicit form is the same
split written as a proof `if`, with plain `step()`s in each case: inside a
case the load has one successor.

Before, `execute()` stopped at the load with "requires exactly one
statement successor", because a planner step refused the split exactly as a
simple `step()` does.

```c filename=a_load_that_may_read_an_earlier_store_splits_into_its_cases.c
int32 g[4];

int32 planned(int32 u) {
    int32 r;
    g[u] = 7;
    r = g[0];
    r = r + 1;
    return r;
}

int32 stepped(int32 u) {
    int32 r;
    g[u] = 7;
    r = g[0];
    r = r + 1;
    return r;
}
```

```click
verifying "a_load_that_may_read_an_earlier_store_splits_into_its_cases.c";

int32 planned(int32 u) {
    requires 0 <= u;
    requires u < 4;
    requires g[0] < 100;
    owns g[0..4];
    ensures result == 8 or to_integer(result) == to_integer(old(g[0]) + 1);
}

int32 stepped(int32 u) {
    requires 0 <= u;
    requires u < 4;
    requires g[0] < 100;
    owns g[0..4];
    ensures result == 8 or to_integer(result) == to_integer(old(g[0]) + 1);
} by {
    step();
    step();
    step();
    if u == 0 {
        step();
        step();
        step();
        close();
    } else {
        step();
        step();
        step();
        close();
    }
}
```

```expect
pass
```
