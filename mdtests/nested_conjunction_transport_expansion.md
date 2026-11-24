# Transport nested conjunctions of scalar facts

```c filename=keep.c
void keep(int *p, int *q, int *r, int *s) { *p = 0; }
```

```click
verifying "keep.c";
void keep(int32* p, int32* q, int32* r, int32* s) {
    owns *p;
    views *q;
    views *r;
    views *s;
    requires separate(memory(*p), memory(*q));
    requires separate(memory(*p), memory(*r));
    requires separate(memory(*p), memory(*s));
    requires *q == 7 and (*r == 8 and *s == 9);
    ensures *q == 7 and (*r == 8 and *s == 9);
} by {
    step();
    have separate(statement(0).footprint, memory(*q)) by {
        close() using { separate(memory(*p), memory(*q)); };
    }
    have separate(statement(0).footprint, memory(*r)) by {
        close() using { separate(memory(*p), memory(*r)); };
    }
    have separate(statement(0).footprint, memory(*s)) by {
        close() using { separate(memory(*p), memory(*s)); };
    }
    have *q == 7 and (*r == 8 and *s == 9) by {
        transport(at(statement(0).entry, *q == 7 and (*r == 8 and *s == 9)), *q == 7 and (*r == 8 and *s == 9));
    }
    step();
    close();
}
```

```expect
pass
```
