# A load inside an `if` condition explains the store that may have changed it

The fact reads `a[m]` only inside the `if` condition. Nothing says `m` and `i`
differ, so `simp` cannot carry it past the store to `a[i]`, and the refusal
still names the read, the store, and the inequality that would separate them,
as it does when the load sits in a branch. The read collector used to visit
only the branches of an `if`, so this refusal printed no explanation.

The companion `an_if_form_fact_survives_a_disjoint_store.md` states `m != i`
and is carried.

```c filename=a_load_in_an_if_condition_explains_the_store.c
void mark_one(int a[], int n, int i, int m) {
    a[i] = 1;
}
```

```click
verifying "a_load_in_an_if_condition_explains_the_store.c";
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires n <= 1073741823;
    requires (if a[m] > 0 { 1 } else { 0 }) == 1;
    consumes a[0..n];
    produces a[0..n];
    ensures (if a[m] > 0 { 1 } else { 0 }) == 1;
} by {
    step();
    have (if a[m] > 0 { 1 } else { 0 }) == 1 by simp();
    execute();
    simp();
}
```

```expect
fail: `a[m]` may have changed since the available fact was stated: the store to `a[i]` may have written it. If `m` and `i` differ, state `m != i`.
```
