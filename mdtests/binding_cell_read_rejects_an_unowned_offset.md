# a proved equality carries only the offsets the arm owns

The positive is
[`binding_cell_read_through_equal_local.md`](binding_cell_read_through_equal_local.md).
Here the equality `identity == parent` is proved exactly as it is there, and
the arm owns exactly one cell of the node, `identity->value` at offset 0. The C
reads `parent->next`, at offset 8.

Retargeting a matched arm's ownership across a proved pointer equality
exchanges two spellings of *one address* (package A22): the arm's clauses are
instantiated at the equal pointer and denote the same cells they always did, at
the offsets the arm states. It grants nothing at any other offset, so the read
of `parent->next` is refused although the block is now the one the C names.
A pointer equality inside one block never reaches the alias index in the first
place — `ConditionTerm::pointer_equal` folds that case to a
`PointerOffsetEqual` — so no offset can be exchanged for another.

```c filename=binding_cell_read_rejects_an_unowned_offset.c
struct cell {
    int32 value;
    struct cell *next;
};

struct cell *read_unowned_offset(struct cell *node, struct cell *parent) {
    struct cell *n;
    n = parent->next;
    return n;
}
```

```click
verifying "binding_cell_read_rejects_an_unowned_offset.c";

spec enum Holder {
    Empty,
    Full(struct cell*, int32),
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
            fact identity != 0;
            fact identity->value == value;
        },
    }
}

struct cell* read_unowned_offset(struct cell* node, struct cell* parent) {
    consumes f: holder_at(node);
    requires f.model != Holder::Empty;
    requires f.model == holder_reroot(f.model, parent);
    produces g: holder_at(node);
    ensures result == result;
} by {
    match f.model {
        Holder::Empty => { contradiction(f.model == Holder::Empty); },
        Holder::Full(identity, value) => {
            have holder_reroot(Holder::Full(identity, value), parent)
                == Holder::Full(parent, value) by {
                unfold(holder_reroot(Holder::Full(identity, value), parent));
                normalize();
            }
            have Holder::Full(identity, value) == Holder::Full(parent, value) by {
                rewrite(Holder::Full(identity, value) == f.model);
                rewrite(f.model == holder_reroot(f.model, parent));
                rewrite(f.model == Holder::Full(identity, value));
                rewrite(holder_reroot(Holder::Full(identity, value), parent)
                    == Holder::Full(parent, value));
                normalize();
            }
            have identity == parent by {
                extract(identity == parent);
            }
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
