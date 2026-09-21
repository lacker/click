# a call that drops the cells does not put the caller back at entry

The pruning step is a call rather than a store: the callee's declared write set
covers `a[0..8]`, so the havoc drops the `a[i]` cell the caller had cached. A
call havoc leaves a marker block in the snapshot, so this shape was refused
before forget marks existed; it is here so that the family covers the havoc
producer as well as the store producer.

```c filename=a_pruned_store_through_a_call_is_not_forgotten.c
void clear_one(int32* a, int32 j) {
    a[j] = 0;
}

int32 read_after_a_call(int32* a, int32 i, int32 j, int32 m) {
    a[i] = 7;
    clear_one(a, j);
    return a[m];
}
```

```click
verifying "a_pruned_store_through_a_call_is_not_forgotten.c";

void clear_one(int32* a, int32 j) {
    owns a[0..8];
    requires 0 <= j;
    requires j < 8;
} by {
    execute();
    simp();
}

int32 read_after_a_call(int32* a, int32 i, int32 j, int32 m) {
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
fail: the call in between may write `a[0..8]`, which is not shown separate from it
```
