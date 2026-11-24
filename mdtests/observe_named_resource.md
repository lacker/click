# Observing a named resource leaves the instance folded

```c filename=observe_named.c
int read_cell(int *p) { return *p; }
```

```click
verifying "observe_named.c";

resource cell(p: int32*) {
    field tag: int32;
    owns *p;
    fact *p == tag;
}

int32 read_cell(int32* p) {
    owns c: cell(p);
    ensures result == old(c.tag);
    ensures c.tag == old(c.tag);
} by {
    observe(c);
    have *p == c.tag by { close(); }
    step_until(function.exit);
    close();
}
```

```expect
pass
```
