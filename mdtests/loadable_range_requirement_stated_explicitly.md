# a range loadability call requirement is a statable goal

`need_cells` requires every in-range byte of its argument to be loadable. The
caller can state that requirement itself, ahead of the call, in the
`loadable(p[a..b])` range form — the same spelling
[surface synthesis](../docs/concepts/expansion.md) recovers for an emitted
call requirement over an external-argument pointer. The written ends survive
the round trip: the range is spelled over the parameter's own name rather
than over a base displaced by its start.

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
    have forall (k: int32) {
        0 <= k and k < len implies loadable(bytes[k..k + 1])
    } by simp;
    execute();
    simp();
}
```

```expect
pass
```
