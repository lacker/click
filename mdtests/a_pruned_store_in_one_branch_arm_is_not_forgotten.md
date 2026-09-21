# a forget on one arm does not frame the read after the join

Only the taken arm writes `a[j]`, so only that arm drops the `a[i]` cell. The
read after the branch must be refused on both arms, and for the same reason:
`a[m]` may be `a[i]`. Before forget marks, the arm that wrote `a[j]` reached a
cell map identical to function entry's and framed the read there, while the arm
that did not kept the cell and was refused — one claim, two answers, decided by
which arm forgot more.

```c filename=a_pruned_store_in_one_branch_arm_is_not_forgotten.c
int32 read_after_a_guarded_store(int32* a, int32 i, int32 j, int32 m, int32 c) {
    a[i] = 7;
    if (c != 0) {
        a[j] = 0;
    }
    return a[m];
}
```

```click
verifying "a_pruned_store_in_one_branch_arm_is_not_forgotten.c";

int32 read_after_a_guarded_store(int32* a, int32 i, int32 j, int32 m, int32 c) {
    owns a[0..8];
    requires 0 <= i;
    requires i < 8;
    requires 0 <= j;
    requires j < 8;
    requires 0 <= m;
    requires m < 8;
    requires m != j;
    ensures result == old(a[m]);
} by {
    execute();
    simp();
}
```

```expect
fail: the store to `a[i]` may have written it. If `m` and `i` differ, state `m != i`
```
