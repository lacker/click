# A pointer-argument body fact is still discharged exactly

The negative for
[`fold_pointer_argument_body_fact.md`](fold_pointer_argument_body_fact.md).
Anchoring a memory-free pure function's pointer arguments to one canonical
snapshot makes the body fact's term *stable*; it does not make the fact free.
Here the proposed model names `other`, a second pointer the contract never
relates to `c`, so `is_owner(Owned::Held(other, 0), c) == 1` is not available
and the fold refuses.

```c filename=owner_cell.c
struct cell {
    int32 value;
};

void clear(struct cell *c, struct cell *other) {
    c->value = 0;
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
            fact p->value == v;
            fact is_owner(model, p) == 1;
        },
    }
}

void clear(struct cell* c, struct cell* other) {
    consumes t: cell_at(c);
    requires t.model != Owned::Free;
    produces u: cell_at(c);
} by {
    match t.model {
        Owned::Free => { contradiction(t.model == Owned::Free); },
        Owned::Held(owner, v) => {
            unfold(t);
            execute();
            let u = fold(cell_at(c), { model: Owned::Held(other, 0) });
            simp();
        },
    }
}
```

```expect
fail: fold requires the instance body facts for the proposed fields
```
