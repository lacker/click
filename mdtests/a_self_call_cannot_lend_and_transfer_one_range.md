# a self-call cannot lend and transfer one range

Recursion is an ordinary entry, so it is checked by the ordinary funnel. `f`
lends `a` and transfers `g`, and its own recursive call passes `g` for `a`.
The planner reserves the owned requirement out of the residual before
planning the view, and the view then has no backing left.

```c filename=a_self_call_cannot_lend_and_transfer_one_range.c
int32 g[4];

void f(int32 a[], int32 n) {
    g[0] = 1;
    if (n > 0) {
        f(g, n - 1);
    }
}
```

```click
verifying "a_self_call_cannot_lend_and_transfer_one_range.c";

void f(int32 a[], int32 n) {
    decreases n;
    requires 0 <= n;
    views a[0..1];
    owns g[0..1];
    ensures g[0] == 1;
} by { execute(); simp(); }
```

```expect
fail: `f.contract` tactic 0: `step()` produced runtime error: stable-view a required resource overlaps a live borrowed footprint refused during planning; selected resource `owns global:g@0[0..1]`
```
