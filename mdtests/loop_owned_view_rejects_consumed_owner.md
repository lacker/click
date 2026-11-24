# A loop-derived view retires when its supporting owner is consumed

The guard conjunction republishes arm views. Consuming the modeled owner
must retire its observation even after that publication and a read-only call.

```c filename=carried.c
int read_cell(int *q) { return *q; }
void consume_cell(int *p);
int caller(int *p, int *q) { while (p != 0 && 1) { read_cell(q); consume_cell(p); return *p; } }
```

```click
verifying "carried.c";
spec enum Model { Empty, Value(int32) }
resource cell(p: int32*) {
    field model: Model;
    match model {
        Model::Empty => { fact p == 0; },
        Model::Value(v) => { owns p[0..1]; fact p[0] == v; },
    }
}
int32 read_cell(int32* q) {
    views q[0..1];
    ensures result == q[0];
}
extern void consume_cell(int32* p) { consumes c: cell(p); }
int32 caller(int32* p, int32* q) {
    requires p != 0;
    consumes c: cell(p);
    owns q[0..1];
    requires c.model != Model::Empty;
    ensures true;
} by {
    loop {
        owns c: cell(p);
        owns q[0..1];
        decreases 0;
        invariant c.model == old(c.model);
        invariant c.model != Model::Empty;
        initialize by close();
        maintain by { step(); step(); step(); }
    }
}
```

```expect
fail: missing resource fact `views p[0]`
```
