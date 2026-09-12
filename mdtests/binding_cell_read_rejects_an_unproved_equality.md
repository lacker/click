# a binding's cells do not follow a disjunction

The positive is
[`binding_cell_read_through_equal_local.md`](binding_cell_read_through_equal_local.md).
Everything here is the same except the clause that pins the payload: it is a
disjunction, `f.model == holder_reroot(f.model, parent) or parent == 0`, so
nothing states exactly that `identity` and `parent` are one address.

Retargeting a matched arm's ownership reads the index of *assumed*
`PointerEqual` facts and nothing else (package A22). A disjunction is not such
a fact, and neither is a disequality: an arm whose payload the path only
constrains keeps its own symbolic spelling, so the cells stay where the arm put
them and the read through `parent` is refused, naming the cell it wanted. That
refusal is the point — a rule that guessed which disjunct held would grant read
authority the path has not established.

```c filename=binding_cell_read_rejects_an_unproved_equality.c
struct cell {
    int32 value;
    struct cell *next;
};

int32 read_through_unproved_local(struct cell *node, struct cell *parent) {
    int32 v;
    v = parent->value;
    return v;
}
```

```click
verifying "binding_cell_read_rejects_an_unproved_equality.c";

spec enum Holder {
    Empty,
    Full(struct cell*, int32),
}

function holder_value(h: Holder) -> int32 {
    match h {
        Holder::Empty => 0,
        Holder::Full(identity, value) => value,
    }
}

function holder_reroot(h: Holder, p: struct cell*) -> Holder {
    match h {
        Holder::Empty => Holder::Empty,
        Holder::Full(identity, value) => Holder::Full(p, value),
    }
}

resource holder_at(child: struct cell*) {
    field model: Holder;
    match model {
        Holder::Empty => { fact child == 0; },
        Holder::Full(identity, value) => {
            owns identity->value;
            owns identity->next;
            fact identity != 0;
            fact identity->value == value;
            fact identity->next == child;
        },
    }
}

int32 read_through_unproved_local(struct cell* node, struct cell* parent) {
    consumes f: holder_at(node);
    requires f.model != Holder::Empty;
    requires f.model == holder_reroot(f.model, parent) or parent == 0;
    requires holder_value(f.model) == 7;
    produces g: holder_at(node);
    ensures result == 7;
} by {
    match f.model {
        Holder::Empty => { contradiction(f.model == Holder::Empty); },
        Holder::Full(identity, value) => {
            unfold(f);
            step();
            step();
            let g = fold(holder_at(node), { model: Holder::Full(identity, value) });
            step();
            simp();
        },
    }
}
```

```expect
fail: missing resource fact
```
