# A `using` premise names an equality in either orientation

`have a == b` and `have b == a` establish one fact, and `rewrite` already
accepts either spelling of an equality it needs. The exact lookup that
discharges a theorem requirement listed in `using` now does too: the
requirement below instantiates to `x == y` and `p == q`, while the proof
holds `y == x` and `q == p`.

```c filename=using_premise_either_orientation.c
struct cell { int32 value; };

int32 same_value(int32 x, int32 y) {
    return x;
}

int32 same_cell(struct cell *p, struct cell *q) {
    return p->value;
}
```

```click
verifying "using_premise_either_orientation.c";

theorem value_symmetric(a: int32, b: int32) {
    requires a == b;

    ensures b == a by { simp(); }
}

theorem cell_symmetric(a: struct cell*, b: struct cell*) {
    requires a == b;

    ensures b == a by { simp(); }
}

int32 same_value(int32 x, int32 y) {
    requires y == x;
    ensures result == y;
} by {
    apply(value_symmetric(x, y)) using { x == y; }
    execute();
    simp();
}

int32 same_cell(struct cell* p, struct cell* q) {
    owns p->value;
    requires q == p;
    ensures result == q->value;
} by {
    apply(cell_symmetric(p, q)) using { p == q; }
    execute();
    simp();
}
```

```expect
pass
```
