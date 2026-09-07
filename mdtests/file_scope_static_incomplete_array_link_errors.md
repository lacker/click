# unresolved file-scope static incomplete arrays are rejected

An incomplete file-scope `static` array cannot be completed by an external
definition with the same C spelling. Internal linkage keeps the two objects
separate, so Click reports the unresolved private array.

```c filename=private.c
static int32 values[];

int32 read() {
    return values[0];
}
```

```c filename=external.c
int32 values[2] = {7, 8};

int32 external_value() {
    return values[0];
}
```

```click
verifying "private.c";
verifying "external.c";

int32 read() {
    ensures result == 0 by auto;
}

int32 external_value() {
    ensures result == 7 by auto;
}
```

```expect
fail: file-scope static array `values` has an incomplete tentative definition but no complete definition in `private.c`
```
