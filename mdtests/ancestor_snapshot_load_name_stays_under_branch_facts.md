# An ancestor-load equality cannot escape its branch fact

The `m != i` arm reads the entry value after the store, while the other arm
aliases the store.  Remembering the entry read before the branch makes the
escape attempt explicit: the false postcondition must be rejected on the
aliasing arm rather than inheriting the distinct arm's load equality.

```c filename=ancestor_snapshot_load_name_stays_under_branch_facts.c
int32 read_after_maybe_aliasing_store(int32* a, int32 i, int32 m) {
    int32 before = a[m];
    a[i] = 7;
    int32 after;
    if (m != i) {
        after = a[m];
    } else {
        after = a[m];
    }
    return after == before;
}
```

```click
verifying "ancestor_snapshot_load_name_stays_under_branch_facts.c";

int32 read_after_maybe_aliasing_store(int32* a, int32 i, int32 m) {
    owns a[0..8];
    requires 0 <= i;
    requires i < 8;
    requires 0 <= m;
    requires m < 8;
    requires a[m] != 7;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: left side evaluated to 0, right side evaluated to 1
```
