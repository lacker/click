# A body fact applying a pure predicate to a pointer is discharged at `fold`

A resource arm may state a fact by applying a pure function to a pointer — the
resource's own parameter, or a pointer payload of the matched constructor. This
is how [D2](../issues/recursive-structure-models.md) states parent/child
consistency inside `rb_at`'s `Node` arm (`rb_parent_is(left_model, p) == 1`)
rather than repeating it in every contract.

`fold` discharges a body fact *exactly*: the proposition it lowers from the arm
must already be an available checked fact. That is why the shape needs a
regression of its own. A pure function's pointer parameter is lowered as an
array-ref argument — memory, pointer, element type — so that a function may
index it. The memory in that triple used to be the ambient snapshot, which made
`is_owner(m, c) == 1` proved before a write and the same proposition demanded by
a `fold` after it two different terms, and every constructor fold refused with
`fold requires the instance body facts for the proposed fields` while the
identical proposition sat in the premise list. A function whose body — and the
body of everything it calls — reads no C memory is a function of its argument
*values*, so its pointer arguments are now anchored to one canonical snapshot
and the two are one term. `is_owner` here is such a function: it compares a
pointer payload with its pointer parameter and reads nothing.

The control in the same file is `peek`, which writes nothing: it verified before
this rule and still does. The negative is
[`fold_pointer_argument_body_fact_rejects_other_owner.md`](fold_pointer_argument_body_fact_rejects_other_owner.md),
where the proposed owner is a pointer that is not provably the cell.

```c filename=owner_cell.c
struct cell {
    int32 value;
};

void clear(struct cell *c) {
    c->value = 0;
}

int32 peek(struct cell *c) {
    return c->value;
}
```

```click
verifying "owner_cell.c";

spec enum Owned {
    Free,
    Held(struct cell*, int),
}

function is_owner(t: Owned, q: struct cell*) -> int32 {
    match t {
        Owned::Free => 1,
        Owned::Held(owner, v) => if owner == q { 1 } else { 0 },
    }
}

resource cell_at(p: struct cell*) {
    field model: Owned;
    match model {
        Owned::Free => { fact p == 0; },
        Owned::Held(owner, v) => {
            owns p->value;
            fact p != 0;
            fact p == owner;
            fact p->value == v;
            fact is_owner(model, p) == 1;
        },
    }
}

void clear(struct cell* c) {
    consumes t: cell_at(c);
    requires t.model != Owned::Free;
    produces u: cell_at(c);
    ensures is_owner(u.model, c) == 1;
} by {
    match t.model {
        Owned::Free => { contradiction(t.model == Owned::Free); },
        Owned::Held(owner, v) => {
            unfold(t);
            have is_owner(Owned::Held(c, 0), c) == 1 by {
                unfold(is_owner(Owned::Held(c, 0), c));
                normalize();
            }
            execute();
            let u = fold(cell_at(c), { model: Owned::Held(c, 0) });
            simp();
        },
    }
}

int32 peek(struct cell* c) {
    owns t: cell_at(c);
    requires t.model != Owned::Free;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Owned::Free => { contradiction(t.model == Owned::Free); },
        Owned::Held(owner, v) => {
            unfold(t);
            execute();
            let t = fold(cell_at(c), { model: old(t.model) });
            simp();
        },
    }
}
```

```expect
pass
```
