# An `if`-form fact survives a store to a different element

A fact about `a[m]` survives the store to `a[i]` when `m != i` is stated,
whatever term reads the cell. The plain form `a[m] > 0` always did. A fact
that reads the same cell inside an `if` condition, or under a bitwise
operator, was not carried: matching the fact across the store compared load
atoms only under `+`, `-` and `*`, and every other term had to be identical,
snapshot included. `simp` refused with "`a[m]` may have changed", though an
explicit `transport` carried the fact.

The refusing companion, with no `m != i`, is
`a_load_in_an_if_condition_explains_the_store.md`.

```c filename=an_if_form_fact_survives_a_disjoint_store.c
void mark_one(int a[], int n, int i, int m) {
    a[i] = 1;
}

void mark_odd(int a[], int n, int i, int m) {
    a[i] = 1;
}
```

```click
verifying "an_if_form_fact_survives_a_disjoint_store.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
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

void mark_odd(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    requires (a[m] & 1) == 1;
    consumes a[0..n];
    produces a[0..n];
    ensures (a[m] & 1) == 1;
} by {
    step();
    have (a[m] & 1) == 1 by simp();
    execute();
    simp();
}
```

```expect
pass
```
