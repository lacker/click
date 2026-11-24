# Transport one conjunct while a discarded conjunct changes

```c filename=keep.c
void keep(int *p, int *q) { *p = 0; }
```

```click
verifying "keep.c";
void keep(int32* p, int32* q) {
    owns *p;
    views *q;
    requires separate(memory(*p), memory(*q));
    requires *p == 8 and *q == 7;
    ensures *q == 7;
} by {
    step();
    have separate(statement(0).footprint, memory(*q)) by {
        close() using { separate(memory(*p), memory(*q)); };
    }
    have *q == 7 by {
        transport(at(statement(0).entry, *p == 8 and *q == 7), *q == 7);
    }
    step();
    close();
}
```

```expect
pass
```
