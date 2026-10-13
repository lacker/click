# A heap claim true in only one alias case is refused

The negative of
[`a_heap_load_after_a_store_that_may_write_its_cell_splits.md`](a_heap_load_after_a_store_that_may_write_its_cell_splits.md).
On the allocated path `r = buf[0]` reads the `7` that `buf[u] = 7` stored
only when `u == 0`; otherwise it reads the `3` stored first. The claim that the
function returns `0` or `7` holds in the first case only, so the case with `u`
not `0` is an ordinary unclosed goal.

```c filename=a_heap_claim_true_in_one_alias_case_is_refused.c
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
verifying "a_heap_claim_true_in_one_alias_case_is_refused.c";

int32 read_back(int32 u) {
    requires 0 <= u;
    requires u < 4;
    ensures result == 0 or result == 7;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == 0 or result == 7` failed for `read_back.ensures_0` path 2: unclosed goal
```
