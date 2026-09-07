# unresolved incomplete multidimensional tentative arrays are rejected

An incomplete multidimensional tentative array definition must be completed
by a fixed-size definition somewhere in the verified source bundle. Without
one, Click cannot materialize its storage and reports the unresolved
definition.

```c filename=reader.c
int32 table[][3];

int32 read() {
    return table[0][0];
}
```

```click
verifying "reader.c";

int32 read() {
    ensures result == 0 by auto;
}
```

```expect
fail: global array `table` has an incomplete tentative definition but no complete definition
```
