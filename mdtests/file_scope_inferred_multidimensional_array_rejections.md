# inferred multidimensional arrays require nested positional groups

An omitted outer dimension can be inferred only from nested positional rows.
Flat, designated, and empty initializers remain outside this slice.

```c filename=bad.c
int32 table[][3] = {1, 2, 3};

int32 read_table() {
    return table[0][0];
}
```

```click
verifying "bad.c";
```

```expect
fail: nested initializer for inferred file-scope multidimensional array `table` expects `1` groups
```
