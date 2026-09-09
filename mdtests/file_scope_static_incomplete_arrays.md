# file-scope static incomplete arrays resolve within one translation unit

An incomplete file-scope `static` array has internal linkage, so a complete
definition must appear in the same translation unit. Once completed, it uses
the same private stable storage as any other file-scope static array.

```c filename=private.c
static int32 values[];

int32 read_incomplete() {
    return values[1];
}

static int32 values[3] = {2, 6, 9};

int32 run() {
    return read_incomplete();
}
```

```click
verifying "private.c";

int32 read_incomplete() {
    requires values[1] == 6;
    ensures result == 6 by auto;
}

int32 run() {
    requires values[1] == 6;
    ensures result == 6 by auto;
}
```

```expect
pass
```
