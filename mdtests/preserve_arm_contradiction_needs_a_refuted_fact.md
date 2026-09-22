# a `contradiction` on a proposition the path does not refute

Reaching a `contradiction` after a prefix of other tactics does not make it
cheap to satisfy. The refutation is decided from the facts standing on the path
at that point, exactly as it is decided for an arm written as `contradiction`
alone: the named proposition and its negation both have to be there.

This arm names `n >= 0`, which the contract requires and the `have` restates,
so it is available — and nothing on the path denies it. The arm stays open, and
the refusal names the proposition as it was written rather than only its
lowered form, so the reader can see which of several `contradiction`s in a body
failed.

```c filename=preserve_arm_contradiction_needs_a_refuted_fact.c
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
verifying "preserve_arm_contradiction_needs_a_refuted_fact.c";

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
        owns l: list_at(node);
        invariant i >= 0;
        invariant i <= n;
        invariant node != 0;

        initialize by simp;
        preserve by {
            match l.model {
                CellList::Nil => {
                    have n >= 0 by { simp(); }
                    contradiction(n >= 0);
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
fail: `contradiction(n >= 0)` requires an exact fact and its exact negation or opposite condition polarity
```
