# a predicate that does not decide an arm refutes nothing

Arm refutation reads only an arm's own binding-free facts against exact
premises; a known value of a pure function over the model refutes no arm.
`list_nonempty_or_null(l.model, node) == 1` holds at loop entry, but the
loop head does not evaluate `list_nonempty_or_null` at each constructor to
look for a contradiction. Here there is none to find anyway: the function is
`1` at both constructors, at `Nil` because the pointer is null and at `Cons`
because the head is this node. The `Nil` arm stays possible, so the body's
proof `match` cannot close it by `contradiction`, and the loop refuses with
the arm rule's own diagnostic.

```c filename=loop_head_predicate_does_not_decide_an_arm.c
struct cell {
    int32 value;
    struct cell* next;
};

void bump_n(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        node->value = 7;
        i = i + 1;
    }
}
```

```click
verifying "loop_head_predicate_does_not_decide_an_arm.c";

spec enum CellList {
    Nil,
    Cons(struct cell*, int32, CellList),
}

function list_nonempty_or_null(xs: CellList, p: struct cell*) -> int32 {
    match xs {
        CellList::Nil => 1,
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
            fact p == identity;
            fact p->value == value;
            fact tail.model == tail_model;
        },
    }
}

void bump_n(struct cell* node, int32 n) {
    requires n >= 0;
    requires n <= 1000;
    requires node != 0;
    owns l: list_at(node);
    requires list_nonempty_or_null(l.model, node) == 1;
} by {
    step();
    step();
    loop {
        owns l: list_at(node);
        invariant i >= 0;
        invariant i <= n;
        invariant node != 0;
        invariant list_nonempty_or_null(l.model, node) == 1;

        initialize by close();
        maintain by {
            match l.model {
                CellList::Nil => { contradiction(l.model == CellList::Nil); },
                CellList::Cons(identity, value, tail_model) => {
                    let { tail: t } = unfold(l);
                    have list_nonempty_or_null(CellList::Cons(node, 7, tail_model), node) == 1 by {
                        unfold(list_nonempty_or_null(CellList::Cons(node, 7, tail_model), node));
                        normalize();
                    }
                    step();
                    step();
                    let l = fold(list_at(node), {
                        model: CellList::Cons(node, 7, tail_model),
                        tail: t
                    });
                },
            }
        }
    }
}
```

```expect
fail: constructor-arm `contradiction` requires an exact fact and its negation in that arm
```
