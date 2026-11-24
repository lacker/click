# Inequality transport expands to preservation and rewriting

```c filename=keep.c
void keep(int *p, int *q) { *p = 0; }
```

```click
verifying "keep.c";
void keep(int32* p, int32* q) {
    owns *p;
    views *q;
    requires separate(memory(*p), memory(*q));
    requires *q > 0;
    ensures *q > 0;
} by {
    step();
    have separate(statement(0).footprint, memory(*q)) by {
        close() using { separate(memory(*p), memory(*q)); };
    }
    have *q > 0 by {
        transport(at(statement(0).entry, *q) > 0, *q > 0);
    }
    step();
    close();
}
```

```expect
pass
```
