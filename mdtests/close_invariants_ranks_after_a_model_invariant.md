# the smart closer ranks a loop whose last invariant has no source form

`close_invariants()` closes a ranking obligation with one arithmetic step,
printed as a source certificate. The obligation compares the measure with its
value at the start of the iteration, which has a source spelling only as
`at(<iteration entry>, i)`.

A bundle member inherits its source form from the whole bundle's. The third
invariant here applies a Click function to a model, which has no source form,
so the bundle has none and neither does any member. Each member is then read
on its own, and the ranking obligations were read without the iteration-entry
context: their arithmetic was planned and then dropped for want of a spelling.
Writing the same invariant first hid the defect, because it is then already an
exact fact and never becomes a member. The clause below is the only ranking
text in the proof.

```c filename=close_invariants_ranks_after_a_model_invariant.c
struct cell {
    int32 value;
    struct cell* next;
};

void probe(struct cell *node, struct cell *other, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}
```

```click
verifying "close_invariants_ranks_after_a_model_invariant.c";

spec enum CellList {
    Nil,
    Cons(struct cell*, int32, CellList),
}

function list_head_is(xs: CellList, p: struct cell*) -> int32 {
    match xs {
        CellList::Nil => if p == 0 { 1 } else { 0 },
        CellList::Cons(identity, value, tail_model) =>
            if identity == p { 1 } else { 0 },
    }
}

resource list_at(p: struct cell*) {
    field model: CellList;
    match model {
        CellList::Nil => { },
        CellList::Cons(identity, value, tail_model) => {
            owns p->value;
            owns &p->next;
            owns tail: list_at(p->next);
            fact identity != 0;
            fact p == identity;
            fact p->value == value;
            fact tail.model == tail_model;
        },
    }
}

void probe(struct cell* node, struct cell* other, int32 n) {
    owns l: list_at(node);
    requires n >= 0;
    requires n <= 1000;
    requires node != 0;
    requires other == 0;
    requires list_head_is(l.model, other) == 1;
    ensures l.model == CellList::Nil;
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns l: list_at(node);
        invariant i >= 0;
        invariant i <= n;
        invariant list_head_is(l.model, other) == 1;

        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
