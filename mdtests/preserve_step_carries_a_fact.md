# Ordinary preservation and rewriting carry an inequality across a store

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
    step() by { close(); }
    have separate(statement(0).footprint, memory(*q)) by {
        close() using { separate(memory(*p), memory(*q)); };
    }
    have *q == at(statement(0).entry, *q) by {
        preserve(memory(*q), statement(0));
    }
    have *q > 0 by {
        rewrite(*q, at(statement(0).entry, *q));
        close();
    }
    step();
    close();
    close(); close(); close(); close();
}
```

```expect
pass
```
