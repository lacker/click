# Symbolic ADT field construction

An unconditional cell body checks a proposed algebraic model against memory.

```c filename=resource_adt_construction.c
void init(int32* p, int32 value) { *p = value; }
void set(int32* p, int32 value) { *p = value; }
void preserve(int32* p) { }
```

```click
verifying "resource_adt_construction.c";

spec enum Mark { Set(int32) }

resource cell(p: int32*) {
    field model: Mark;
    owns p[0..1];
    fact model == Mark::Set(p[0]);
}

void init(int32* p, int32 value) {
    consumes p[0..1];
    produces c: cell(p);
    ensures c.model == Mark::Set(value);
} by {
    execute();
    let c = fold(cell(p), { model: Mark::Set(value) });
    simp();
}

void set(int32* p, int32 value) {
    owns c: cell(p);
    ensures c.model == Mark::Set(value);
} by {
    unfold(c);
    execute();
    let c = fold(cell(p), { model: Mark::Set(value) });
    simp();
}

void preserve(int32* p) {
    owns c: cell(p);
    ensures c.model == old(c.model);
} by {
    unfold(c);
    let c = fold(cell(p), { model: old(c.model) });
    execute();
    simp();
}
```

```expect
pass
```
