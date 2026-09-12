# a predicate fact refutes an arm that has bindings

[`loop_head_predicate_refutes_an_arm.md`](loop_head_predicate_refutes_an_arm.md)
refutes a constructor with no fields, whose value the predicate decides on its
own. This is the other half: the arm refuted here is `CellList::Cons`, whose
head pointer is a binding, and what decides it is the arm's *own* fact about
that binding.

An owned folded instance's body holds wherever the instance is held, so if the
model were `Cons(identity, ..)` then `fact p == identity` would hold of that
`identity`. Refutation reads the arm that way: the bindings are symbolic, the
arm's own facts are premises, and `list_head_is`'s body at `Cons` is
`if identity == other { 1 } else { 0 }`. Here the arm says `identity != 0` while the
requirements say `other` is null; one null and one non-null pointer
are different (package A11), so the body is `0` where the invariant says `1`.

`Cons` is refuted, `Nil` is the one arm left, and because `Nil` names no fields
the loop's exit then says what the model *is*, not only what it is not. That
positive conclusion is what an ascending walk needs at its own exit, where the
frames it climbed through are the arms with bindings and `Context::Top` is the
one that survives. Nothing here mentions `Nil`'s own body, which is empty.

```c filename=contract_predicate_refutes_a_framed_arm.c
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
verifying "contract_predicate_refutes_a_framed_arm.c";

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
            owns p->next;
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
