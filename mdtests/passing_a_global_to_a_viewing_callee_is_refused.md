# passing an owned global to a callee that views it is refused at the call

A callee that declares `views a[0..n]` beside `owns g[0..1]` cannot be called
with `g` as `a`: the caller would have to lend a view of the same bytes it
hands over as the owned global. The loan planner refuses that call, so the
caller cannot reach the callee's postcondition at all.

This is the call-site half of `global_may_alias_an_array_argument.md`, where
the callee declares no resource for `a` and the refusal has to come from the
body instead.

```c filename=passing_a_global_to_a_viewing_callee.c
int32 g[4];

void f(int32 a[], int32 n) {
    g[0] = 1;
}

void caller() {
    f(g, 4);
}
```

```click
verifying "passing_a_global_to_a_viewing_callee.c";

void f(int32 a[], int32 n) {
    requires 0 < n;
    views a[0..n];
    owns g[0..1];
    ensures g[0] == 1;
} by { execute(); simp(); }

void caller() {
    owns g[0..4];
    ensures g[0] == 1;
} by { execute(); simp(); }
```

```expect
fail: a required resource overlaps a live borrowed footprint
```
