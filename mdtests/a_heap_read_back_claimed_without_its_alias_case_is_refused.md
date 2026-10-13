# A heap read back claimed without its alias case is refused

The negative of
[`a_heap_load_after_a_store_that_may_write_its_cell_splits.md`](a_heap_load_after_a_store_that_may_write_its_cell_splits.md).
A read of `buf[0]` sees past `buf[u] = 7` to the earlier `3` only where the
path's facts place the store off the cell. On the allocated path with
`u == 0` the read is the `7`, so the claim that the function returns `0` or
the earlier `3` is refused at that case, path 1: path 0 is the failed
allocation and path 2 the case `u != 0`, where the read is the `3`.

```c filename=a_heap_read_back_claimed_without_its_alias_case_is_refused.c
int32 read_back(int32 u) {
    int32 r;
    int32* buf;
    buf = malloc(16);
    if (buf == 0) {
        return 0;
    }
    buf[0] = 3;
    buf[u] = 7;
    r = buf[0];
    free(buf);
    return r;
}
```

```click
verifying "a_heap_read_back_claimed_without_its_alias_case_is_refused.c";

int32 read_back(int32 u) {
    requires 0 <= u;
    requires u < 4;
    ensures result == 0 or result == 3;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == 0 or result == 3` failed for `read_back.ensures_0` path 1
```
