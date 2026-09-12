# a predicate fact refutes an arm of the binder's model

Arm refutation reads a path fact against an arm's *own* fact: `list_at`'s
`Nil` arm says `p == 0`, so `node != 0` says the model is not `Nil`. That
route needs the arm to state something about a name the path already talks
about, and a model keyed by its own payload does not: the arm's facts are
about its bindings.

What such a section does have is a predicate over the model. `list_head_is`
is `1` exactly when its pointer argument is the list's head — the null pointer
for `Nil`, the node's own identity for `Cons` — so
`requires list_head_is(l.model, node) == 1;` plus `node != 0` says the model
is not `Nil`, and the same two premises say it at the loop head, where the
invariants play the part of the requirements. Evaluating `list_head_is`'s
declared body at `CellList::Nil` gives `if node == 0 { 1 } else { 0 }`, which
this path decides to be `0`; the premise says `1`, so the arm is refuted and
the body's proof `match` closes it by `contradiction` without unfolding a
list it would then have to refold.

The `Nil` arm here states nothing of its own, so the older route has nothing
to work with and this is the only reason the arm closes.

```c filename=loop_head_predicate_refutes_an_arm.c
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
verifying "loop_head_predicate_refutes_an_arm.c";

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
    requires list_head_is(l.model, node) == 1;
} by {
    step();
    step();
    loop {
        owns l: list_at(node);
        invariant i >= 0;
        invariant i <= n;
        invariant node != 0;
        invariant list_head_is(l.model, node) == 1;

        initialize by simp;
        preserve by {
            match l.model {
                CellList::Nil => { contradiction(l.model == CellList::Nil); },
                CellList::Cons(identity, value, tail_model) => {
                    unfold(l) as { tail: t };
                    have list_head_is(CellList::Cons(node, 7, tail_model), node) == 1 by {
                        unfold(list_head_is(CellList::Cons(node, 7, tail_model), node));
                        normalize();
                    }
                    step();
                    step();
                    let l = fold(list_at(node), {
                        model: CellList::Cons(node, 7, tail_model)
                    }, { tail: t });
                    close_invariants();
                },
            }
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
