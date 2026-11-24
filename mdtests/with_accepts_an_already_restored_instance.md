# A `with` scope accepts an explicitly restored instance

An explicit `fold(c)` restores the instance inside either scope. The first
scope closes before the function exit and the second scope closes at return.

```c filename=with_already_restored.c
int read_cell(int *p) { int n = *p; return n; }
int read_at_return(int *p) { return *p; }
```

```click
verifying "with_already_restored.c";

resource cell(p: int32*) {
    field tag: int32;
    owns *p;
}

int32 read_cell(int32* p) {
    owns c: cell(p);
    ensures c.tag == old(c.tag);
} by {
    with(c) {
        step();
        fold(c);
    }
    step_until(function.exit);
    close();
}

int32 read_at_return(int32* p) {
    owns c: cell(p);
    ensures c.tag == old(c.tag);
} by {
    with(c) {
        step_until(function.exit);
        fold(c);
    }
    close();
}
```

```expect
pass
```
