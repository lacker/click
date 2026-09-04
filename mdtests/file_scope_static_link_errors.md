# File-scope static globals do not satisfy extern declarations in another file

An internal-linkage object is not a definition of an externally linked object
with the same spelling in another translation unit.

```c filename=owner.c
static int32 counter = 1;

int32 owner_value() {
    return counter;
}
```

```c filename=reader.c
extern int32 counter;

int32 reader_value() {
    return counter;
}
```

```click
verifying "owner.c";
verifying "reader.c";
```

```expect
fail: global `counter` is declared `extern` but has no definition
```
