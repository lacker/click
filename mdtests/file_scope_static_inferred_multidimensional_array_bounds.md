# file-scope static multidimensional arrays can infer private outer bounds

A file-scope `static` multidimensional definition may omit its outer bound
when nested positional initializer rows provide it. Its storage remains
private, even when another source defines an external array with the same name.

```c filename=private.c
static int32 table[][3] = {{1, 2}, {4, 5, 6}};

int32 read_private_table() {
    return table[0][2] + table[1][2];
}
```

```c filename=external.c
int32 table[2][3] = {{10, 11, 12}, {13, 14, 15}};

int32 read_external_table() {
    return table[0][2] + table[1][2];
}
```

```click
verifying "private.c";
verifying "external.c";

int32 read_private_table() {
    ensures result == 6 by auto;
}

int32 read_external_table() {
    ensures result == 27 by auto;
}
```

```expect
pass
```
