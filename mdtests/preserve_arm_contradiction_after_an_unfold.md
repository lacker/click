# a `contradiction` on the fact the arm's own `unfold` exposed

The refuting fact does not have to be standing at the loop head in the arm's
own spelling. Here it is `list_at`'s own `CellList::Nil` arm that says
`fact p == 0`, and the proof reaches it the direct way: inside the `Nil` arm,
`unfold(l)` publishes that arm's body, `node == 0` lands on the path, and it is
the loop's `invariant node != 0` that refutes it. The `contradiction` names
`node != 0`, a C-level disequality, rather than a model equation.

That is the shape an insert fixup needs, where the refutation lives one layer
down in the instance and only the `unfold` brings it up. It is exactly what an
arm-planning pattern match over `[contradiction(..)]` could not express: the
bridging tactic has to run before the refutation exists. The preservation
driver closes the path at the `contradiction` instead, so the prefix runs
first and the arm still owes nothing to the back edge.
[`preserve_arm_contradiction_after_a_have.md`](preserve_arm_contradiction_after_a_have.md)
is the same lifting with a `have` as the prefix, and
[`preserve_arm_contradiction_needs_a_refuted_fact.md`](preserve_arm_contradiction_needs_a_refuted_fact.md)
is what happens when the named proposition is not refuted at all.

```c filename=preserve_arm_contradiction_after_an_unfold.c
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
verifying "preserve_arm_contradiction_after_an_unfold.c";

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
            owns &p->next;
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
        decreases n - i;
        owns l: list_at(node);
        invariant i >= 0;
        invariant i <= n;
        invariant node != 0;

        initialize by simp;
        preserve by {
            match l.model {
                CellList::Nil => {
                    unfold(l);
                    contradiction(node != 0);
                },
                CellList::Cons(identity, value, tail_model) => {
                    let { tail: t } = unfold(l);
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
