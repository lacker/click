# a cell fact from after one store does not survive the next store to it

Each snapshot names its own read of a cell, so the value this proof reads after
the first store is not the value it reads after the second. A read that kept one
identity across both stores would make the stale fact available here.

```c filename=a_second_store_replaces_the_first_cell_value.c
void mark_twice(int32 a[], int32 n, int32 i) {
    a[i] = 1;
    a[i] = 2;
}
```

```click
verifying "a_second_store_replaces_the_first_cell_value.c";

void mark_twice(int32 a[], int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    requires n <= 1073741823;
    requires loadable(a[0..n]);
    consumes a[0..n];
    produces a[0..n];
} by {
    step();
    have a[i] == 1 by { simp(); }
    step();
    have a[i] == 1 by { simp(); }
    execute();
    simp();
}
```

```expect
fail: tactic 3: `have` failed for `a[i] == 1`
```
