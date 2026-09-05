# const global table writes are rejected

The source boundary must reject mutation of an immutable file-scope table.

```c filename=const_table.c
const int32 table[2] = {1, 2};

int32 bad() {
    table[0] = 3;
    return table[0];
}
```

```click
verifying "const_table.c";
```

```expect
fail:const-qualified
```
