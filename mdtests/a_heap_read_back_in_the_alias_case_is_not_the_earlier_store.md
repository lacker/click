# A heap read back in the alias case is not the earlier store

The negative of
[`a_read_back_across_a_store_that_misses_its_cell_is_the_earlier_store.md`](a_read_back_across_a_store_that_misses_its_cell_is_the_earlier_store.md).
In the case `u == 0` the store `buf[u] = 7` wrote `buf[0]`, so the read is
the `7`. Claiming the earlier `3` there is refused as false, not merely
unproved.

```c filename=a_heap_read_back_in_the_alias_case_is_not_the_earlier_store.c
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
verifying "a_heap_read_back_in_the_alias_case_is_not_the_earlier_store.c";

int32 read_back(int32 u) {
    requires 0 <= u;
    requires u < 4;
    ensures result == 0 or result == 7 or result == 3;
} by {
    step();
    step();
    step();
    if buf == 0 {
    } else {
        step();
        step();
        step();
        step();
        if u == 0 {
            step();
            have r == 3;
            step();
            step();
            close();
        } else {
            step();
            step();
            step();
            close();
        }
    }
}
```

```expect
fail: it is false at this point
```
