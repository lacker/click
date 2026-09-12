# a cell owned on a binding is read through a C local proved equal

A matched arm may own the cells of the node its own payload carries, so
`Holder::Full(identity, value)` owns `identity->value`. `identity` is a
*binding*: at an arbitrary proof frontier it is a fresh symbolic pointer that no
C statement is written through. The C here reads `parent->value`, and the two
spellings are one address only because the contract pins the payload —
`f.model == holder_reroot(f.model, parent)` gives
`Full(identity, value) == Full(parent, value)`, and `extract` takes the field
equality `identity == parent` out of it by constructor injectivity.

An exact pointer equality between the binding and a C object makes the arm's
clauses denote that object's cells, so `unfold` owns, names, and states them at
the spelling the C reads (package A22; see
[`docs/concepts/resources.md`](../docs/concepts/resources.md)). Without the
rule the read is refused with `missing resource fact views
symbolic-pointer:…`, with ownership of the very cell held one provable
equality away. The refold is the same rule from the other side: it requires the
arm's cells and facts at that spelling too, so the walk can hand the instance
back.

This is the reduction of [`rb_ascending_walk_to_root.md`](rb_ascending_walk_to_root.md),
where every iteration reads the frame's node through the C local the loop
reassigns. The negatives are
[`binding_cell_read_rejects_an_unproved_equality.md`](binding_cell_read_rejects_an_unproved_equality.md)
and [`binding_cell_read_rejects_a_different_offset.md`](binding_cell_read_rejects_a_different_offset.md).

```c filename=binding_cell_read_through_equal_local.c
struct cell {
    int32 value;
    struct cell *next;
};

int32 read_through_equal_local(struct cell *node, struct cell *parent) {
    int32 v;
    v = parent->value;
    return v;
}
```

```click
verifying "binding_cell_read_through_equal_local.c";

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

int32 read_through_equal_local(struct cell* node, struct cell* parent) {
    consumes f: holder_at(node);
    requires f.model != Holder::Empty;
    requires f.model == holder_reroot(f.model, parent);
    requires holder_value(f.model) == 7;
    produces g: holder_at(node);
    ensures result == 7;
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
            have holder_value(Holder::Full(identity, value)) == value by {
                unfold(holder_value(Holder::Full(identity, value)));
                normalize();
            }
            have value == 7 by {
                rewrite(value == holder_value(Holder::Full(identity, value)));
                rewrite(Holder::Full(identity, value) == f.model);
                assumption();
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
pass
```
