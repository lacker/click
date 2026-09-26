# a store at a symbolic index of a seeded constant range is not framed

A store to `a[i]` may write any element of the run seeded for
`owns a[0..1000]`, so the read of `a[0]` after it does not keep its entry
value: `i` may be `0`. `result == old(a[0])` is refused.

```c filename=a_store_at_a_symbolic_index_of_a_constant_range_is_not_framed.c
int32 store_then_read(int32* a, int32 i) {
    a[i] = 7;
    return a[0];
}
```

```click
verifying "a_store_at_a_symbolic_index_of_a_constant_range_is_not_framed.c";

int32 store_then_read(int32* a, int32 i) {
    owns a[0..1000];
    requires 0 <= i;
    requires i < 1000;
    ensures result == old(a[0]);
} by {
    execute();
    simp();
}
```

```expect
fail: result == old(a[0])
```
