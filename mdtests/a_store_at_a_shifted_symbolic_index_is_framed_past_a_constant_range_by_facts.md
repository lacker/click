# a store at a shifted symbolic index is framed past a seeded constant range by facts

The store `a[k + 1] = 7` writes element `k + 1` of the run seeded for
`owns a[0..1000000]`. The bounds on `k` place the store among elements 1 to
10, so every other element keeps its entry value without being asked about,
and only those ten are asked one by one. With `k >= 5` the store misses `a[5]`
and the read keeps its entry value. Without it, `k` may be `4` and
`result == old(a[5])` is refused.

```c filename=a_store_at_a_shifted_symbolic_index_is_framed_past_a_constant_range_by_facts.c
int32 apart(int32* a, int32 k) {
    a[k + 1] = 7;
    return a[5];
}

int32 maybe_aliased(int32* a, int32 k) {
    a[k + 1] = 7;
    return a[5];
}
```

```click
verifying "a_store_at_a_shifted_symbolic_index_is_framed_past_a_constant_range_by_facts.c";

int32 apart(int32* a, int32 k) {
    owns a[0..1000000];
    requires 5 <= k and k < 10;
    ensures result == old(a[5]);
} by {
    execute();
    simp();
}

int32 maybe_aliased(int32* a, int32 k) {
    owns a[0..1000000];
    requires 0 <= k and k < 10;
    ensures result == old(a[5]);
} by {
    execute();
    simp();
}
```

```expect
fail: result == old(a[5])
```
