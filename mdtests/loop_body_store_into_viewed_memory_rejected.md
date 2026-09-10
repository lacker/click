# A loop body store into viewed memory is rejected at the store

Bounding the default loop havoc by ownership does not grant the body any write
authority. The function only views `r`, so the store `r[i] = i` inside the loop
has no owned range covering it and is rejected at the store, not framed away by
the loop footprint.

```c filename=loop_body_store_into_viewed_memory_rejected.c
void loop_body_store_into_viewed_memory_rejected(int32 r[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        r[i] = i;
        i = i + 1;
    }
}
```

```click
verifying "loop_body_store_into_viewed_memory_rejected.c";

void loop_body_store_into_viewed_memory_rejected(int32 r[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(r[0..n]);
    views r[0..n];
} by {
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
    }
    step();
    simp();
}
```

```expect
fail: missing resource fact
```
