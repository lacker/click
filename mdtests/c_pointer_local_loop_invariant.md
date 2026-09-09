# preserve a pointer/index relation across a loop

An explicit invariant can relate a pointer local that is advanced by the loop
to the current array index.

The preservation proof's `simp` emits `arithmetic() using` with the entry
pointer relation and strict index bound. The bound excludes index overflow;
the checked step compares exact byte advances, not wrapped int32 offsets.

```c filename=c_pointer_local_loop_invariant.c
int32 last_element(int32 arr[], int32 n, int32 cap) {
    int32* p;
    int32 i;
    p = arr;
    i = 0;
    while (i < n) {
        i = i + 1;
        p = p + 1;
    }
    return *p;
}
```

```click
verifying "c_pointer_local_loop_invariant.c";

int32 last_element(int32 arr[], int32 n, int32 cap) {
    requires 0 <= n;
    requires n < cap;
    requires 1 <= cap;
    requires ((uint32)cap) <= 1073741823u32;
    views arr[0..cap];
    ensures result == arr[n];
} by {
    step();
    step();
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
        invariant p == arr + i;
        preserve by {
            step();
            step();
            have p == arr + i by simp;
            close_invariants by { simp(); }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
