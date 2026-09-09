# multidimensional array indices stay within their declared subobjects

```c filename=t.c
int32 c() {
    int32 m[2][3];
    m[1][2] = 1;
    m[0][5] = 9;
    return m[1][2];
}
```

```click
verifying "t.c";

int32 c() {
    ensures result == 9;
}
```

```expect
fail: array subobject index
```
