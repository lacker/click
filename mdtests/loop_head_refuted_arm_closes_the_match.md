# a loop head's premises refute an arm of the binder's model

At an arbitrary loop head a binder's model is a fresh symbolic value, and the
invariants play the part of a contract's requirements when an arm is selected.
The same premises decide the reverse: one that contradicts an arm's own fact
says the binder's model is not that constructor.

`list_at`'s `List::Nil` arm states `fact p == 0`, so `invariant node != 0`
publishes `l.model != CellList::Nil` at the loop head. The body's proof `match`
then closes the `Nil` arm by `contradiction` on the model, exactly as a
contract-level `match` does. Without that premise the arm could only be closed
by unfolding the instance first, and a `contradiction` on a live arm is not a
checked preservation operation.

```c filename=loop_head_refuted_arm_closes_the_match.c
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
verifying "loop_head_refuted_arm_closes_the_match.c";

spec enum CellList {
    Nil,
    Cons(struct cell*, int32, CellList),
}

resource list_at(p: struct cell*) {
    field model: CellList;
    match model {
        CellList::Nil => { fact p == 0; },
        CellList::Cons(identity, value, tail_model) => {
            owns p->value;
            owns p->next;
            owns tail: list_at(p->next);
            fact p != 0;
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
    requires l.model != CellList::Nil;
} by {
    step();
    step();
    loop {
        owns l: list_at(node);
        invariant i >= 0;
        invariant i <= n;
        invariant node != 0;

        initialize by simp;
        preserve by {
            match l.model {
                CellList::Nil => { contradiction(l.model == CellList::Nil); },
                CellList::Cons(identity, value, tail_model) => {
                    unfold(l) as { tail: t };
                    step();
                    step();
                    let l = fold(list_at(node), {
                        model: CellList::Cons(identity, 7, tail_model)
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
