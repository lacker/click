# A read back across a store that misses its cell is the earlier store

`buf[0] = 3; buf[u] = 7; r = buf[0];` reads `7` when `u == 0` and the `3`
otherwise, whichever object `buf` is. The twins below are the same program
over a file-scope array and over a `malloc` buffer, each proved twice: by
the omitted proof, and with the case split written as a proof `if` after the store
has run, so the case `u != 0` is learned only after `buf[u] = 7` dropped the
cached `buf[0]`.

In that case the load reads the cell from the recorded history under the
path's facts: `u != 0` places the store off `buf[0]`, and the cell's value
before it is the `3`. Before, only the file-scope twin verified, and only
because its reduced memory happened to equal the state before the store;
the heap store also records the bytes it initialized, so the heap twin's
`have r == 3` was refused. A `calloc` buffer reads the same `3`, not the zero
it was allocated with: the store `buf[0] = 3` replaced that zero, and the
history says so.

```c filename=a_read_back_across_a_store_that_misses_its_cell_is_the_earlier_store.c
int32 g[4];

int32 global_planned(int32 u) {
    int32 r;
    g[0] = 3;
    g[u] = 7;
    r = g[0];
    return r;
}

int32 global_stepped(int32 u) {
    int32 r;
    g[0] = 3;
    g[u] = 7;
    r = g[0];
    return r;
}

int32 heap_planned(int32 u) {
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

int32 heap_stepped(int32 u) {
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
int32 zeroed_heap_planned(int32 u) {
    int32 r;
    int32* buf;
    buf = calloc(4, 4);
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
verifying "a_read_back_across_a_store_that_misses_its_cell_is_the_earlier_store.c";

int32 global_planned(int32 u) {
    requires 0 <= u;
    requires u < 4;
    owns g[0..4];
    ensures u != 0 or result == 7;
    ensures u == 0 or result == 3;
}

int32 global_stepped(int32 u) {
    requires 0 <= u;
    requires u < 4;
    owns g[0..4];
    ensures result == 7 or result == 3;
} by {
    step();
    step();
    step();
    step();
    if u == 0 {
        step();
        have r == 7;
        step();
        solve();
    } else {
        step();
        have r == 3;
        step();
        solve();
    }
}

int32 heap_planned(int32 u) {
    requires 0 <= u;
    requires u < 4;
    ensures result == 0 or u != 0 or result == 7;
    ensures result == 0 or u == 0 or result == 3;
}

int32 heap_stepped(int32 u) {
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
            have r == 7;
            step();
            step();
            solve();
        } else {
            step();
            have r == 3;
            step();
            step();
            solve();
        }
    }
}
int32 zeroed_heap_planned(int32 u) {
    requires 0 <= u;
    requires u < 4;
    ensures result == 0 or u != 0 or result == 7;
    ensures result == 0 or u == 0 or result == 3;
}
```

```expect
pass
```
