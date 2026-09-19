# fill3 verifies a three-element store loop

This checks a three-cell write permission for three `int32` array-index stores
and a final array-index load. The `consumes` clause is the only readability the
loads need: a held resource answers them directly.

```c filename=fill3.c
int32 fill3(int32* p) {
    int32 i;
    i = 0;
    while (i < 3) {
        p[i] = i;
        i = i + 1;
    }
    return p[2];
}
```

```click
verifying "fill3.c";

int32 fill3(int32* p) {
    consumes p[0..3];
    ensures returns_second: result == 2 by auto;
}
```

```expect
pass
```
