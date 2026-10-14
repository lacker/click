# A read back across a store no fact places stays unknown

A read sees past a store to an earlier one only where the path's facts place
the store off the cell. Here `buf[0] = 3` is followed by two stores at
symbolic indices, and the read `r = buf[0]` splits only on the cell it can
still see, `buf[v]`. The case `v != 0` sees past `buf[v] = 9`, but no fact
relates `u` to `0`, so `buf[u] = 7` may have written the cell and the read is
unknown. The claim that it is the `3` whenever neither index is `0` is
therefore refused, at the case whose facts name `v` and not `u`.

```c filename=a_read_back_across_a_store_no_fact_places_stays_unknown.c
int32 read_back(int32 u, int32 v) {
    int32 r;
    int32* buf;
    buf = malloc(16);
    if (buf == 0) {
        return 0;
    }
    buf[0] = 3;
    buf[u] = 7;
    buf[v] = 9;
    r = buf[0];
    free(buf);
    return r;
}
```

```click
verifying "a_read_back_across_a_store_no_fact_places_stays_unknown.c";

int32 read_back(int32 u, int32 v) {
    requires 0 <= u;
    requires u < 4;
    requires 0 <= v;
    requires v < 4;
    ensures result == 0 or u == 0 or v == 0 or result == 3;
} by {
    execute();
    simp();
}
```

```expect
fail: case: [at(statement(2).exit, buf) != 0, 0 != v]
```
