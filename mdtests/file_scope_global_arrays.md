# file-scope scalar arrays have stable initialized storage

Fixed-size scalar arrays at file scope use one stable memory block. Indexed
reads see the literal or zero-filled initializer, and indexed writes require a
matching mutable footprint.

```c filename=table.c
int32 table[3] = {2, 4};

int32 read_middle() {
    return table[1];
}

int32 increment_middle() {
    table[1] = table[1] + 1;
    return table[1];
}
```

```click
verifying "table.c";

int32 read_middle() {
    ensures result == 4 by auto;
}

int32 increment_middle() {
    mutable table[0..3] by auto;
    ensures result == old(table[1]) + 1 by auto;
    ensures table[1] == old(table[1]) + 1 by auto;
}
```

```expect
pass
```
