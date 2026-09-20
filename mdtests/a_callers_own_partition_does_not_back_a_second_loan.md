# a caller's own entry partition does not back a second loan

`a_caller_cannot_lend_and_transfer_one_range.md` from a caller that holds an
entry partition of its own. `caller` lends `a` and transfers `g`, so its body
runs with `separate(memory(g[0..4]), memory(a[0..1]))` among its facts. That
fact says nothing about `g` against `g`, and the planner asks about `g`
against `g`: it reserves the callee's `owns g[0..1]` out of the residual and
then cannot find backing for the callee's `views g[0..1]` in what is left.

The checked point is that a separation the caller holds is never mistaken for
the backing a loan needs.

```c filename=a_callers_own_partition_does_not_back_a_second_loan.c
int32 g[4];

void split(int32 *b) {
    g[0] = 1;
}

void caller(int32 a[], int32 n) {
    split(g);
}
```

```click
verifying "a_callers_own_partition_does_not_back_a_second_loan.c";

void split(int32* b) {
    views b[0..1];
    owns g[0..1];
    ensures g[0] == 1;
} by { execute(); simp(); }

void caller(int32 a[], int32 n) {
    requires 0 < n;
    requires a[0] == 5;
    views a[0..1];
    owns g[0..4];
    ensures a[0] == 5;
} by { execute(); simp(); }
```

```expect
fail: `caller.contract` tactic 0: `step()` produced runtime error: stable-view a required resource overlaps a live borrowed footprint refused during planning; selected resource `owns global:g@0[0..1]`
```
