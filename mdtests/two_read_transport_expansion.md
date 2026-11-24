# Transport a comparison between two preserved reads

```c filename=keep.c
void keep(int *p, int *q, int *r) { *p = 0; }
```

```click
verifying "keep.c";
void keep(int32* p, int32* q, int32* r) {
    owns *p;
    views *q;
    views *r;
    requires separate(memory(*p), memory(*q));
    requires separate(memory(*p), memory(*r));
    requires *q == *r;
    ensures *q == *r;
} by {
    step();
    have separate(statement(0).footprint, memory(*q)) by {
        close() using { separate(memory(*p), memory(*q)); };
    }
    have separate(statement(0).footprint, memory(*r)) by {
        close() using { separate(memory(*p), memory(*r)); };
    }
    have *q == *r by {
        transport(at(statement(0).entry, *q == *r), *q == *r);
    }
    step();
    close();
}
```

```expect
pass
```
