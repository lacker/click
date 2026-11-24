# Transport an implication by preserving guard and conclusion

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
    requires *q == 7 implies *r == 8;
    ensures *q == 7 implies *r == 8;
} by {
    step();
    have separate(statement(0).footprint, memory(*q)) by {
        close() using { separate(memory(*p), memory(*q)); };
    }
    have separate(statement(0).footprint, memory(*r)) by {
        close() using { separate(memory(*p), memory(*r)); };
    }
    have *q == 7 implies *r == 8 by {
        transport(at(statement(0).entry, *q == 7 implies *r == 8), *q == 7 implies *r == 8);
    }
    step();
    close();
}
```

```expect
pass
```
