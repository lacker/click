# Guarded universal range loadability

```c filename=forall_loadable_range.c
int32 range_probe(uint8 bytes[], int32 len) {
    return need_cells(bytes, len);
}
```

```click
verifying "forall_loadable_range.c";

extern int32 need_cells(uint8 bytes[], int32 len) {
    requires forall (k: int32) {
        0 <= k and k < len implies loadable(bytes[k..k + 1])
    };
    ensures result == 0;
}

int32 range_probe(uint8 bytes[], int32 len) {
    requires loadable(bytes[0..len + 1]);
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
