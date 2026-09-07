# unresolved incomplete tentative arrays are rejected

An incomplete tentative array definition must be completed by a fixed-size
definition somewhere in the verified source bundle. Without one, Click cannot
materialize the array's storage and reports the unresolved definition.

```c filename=reader.c
int32 values[];

int32 read() {
    return values[0];
}
```

```click
verifying "reader.c";

int32 read() {
    ensures result == 0 by auto;
}
```

```expect
fail: global array `values` has an incomplete tentative definition but no complete definition
```
