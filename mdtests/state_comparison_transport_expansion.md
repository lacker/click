# Whole-fact state transport expands to preservation and rewriting

```c filename=keep.c
void keep(int *p, int *q) { *p = 0; }
```

```click
verifying "keep.c";
void keep(int32* p, int32* q) {
    owns *p;
    views *q;
    requires separate(memory(*p), memory(*q));
    requires *q == 7;
    ensures *q == 7;
} by {
    step();
    have separate(statement(0).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have *q == 7 by {
        transport(at(statement(0).entry, *q == 7), *q == 7) using {
            at(statement(0).entry, *q == 7);
            separate(statement(0).footprint, memory(*q));
        };
    }
    step();
    known();
}
```

```expect
pass
```
