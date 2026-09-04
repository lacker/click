# Existential witness transport for range loadability

```c filename=exists_loadable_range.c
int32 range_probe(uint8 bytes[], int32 len) {
    return need_cells(bytes);
}
```

```click
verifying "exists_loadable_range.c";

extern int32 need_cells(uint8 bytes[]) {
    requires exists (len: int32) {
        forall (k: int32) {
            0 <= k and k < len implies loadable(bytes[k..k + 1])
        }
    };
    ensures result == 0;
}

int32 range_probe(uint8 bytes[], int32 len) {
    requires exists (length: int32) {
        loadable(bytes[0..length + 1])
    };
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
