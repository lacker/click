# a `contradiction` closes its arm after a prefix of other tactics

This is
[`loop_head_refuted_arm_closes_the_match.md`](loop_head_refuted_arm_closes_the_match.md)
with one `have` placed in front of its `contradiction`. The loop head still
refutes the `CellList::Nil` arm, the `have` is still true, and the
`contradiction` still names the refuted model equation — and the arm still
closes.

A `contradiction` refutes the path it stands on, wherever on that path it
stands. `plan_execution_match` in `src/surface/proof/proof_object/match_cases.rs`
still recognizes an arm written as exactly `[contradiction(..)]` and keeps that
constructor out of the frontier split altogether, which costs nothing to run.
An arm with a prefix is an ordinary live arm instead, and the preservation
driver closes it where the `contradiction` is reached: the path is refuted, so
it owes no invariant and no measure, and contributes neither a back edge nor a
loop exit. Nothing after it on that path is executed or proved.

The restriction that this fixture used to pin bit whenever the fact that
refutes an arm has to be bridged into the arm's own spelling first, which is
the usual shape when the refuting premise is about an instance field and the
arm substitutes a constructor for it.
[`preserve_arm_contradiction_after_an_unfold.md`](preserve_arm_contradiction_after_an_unfold.md)
is that shape with the bridging `unfold` written out.

```c filename=preserve_arm_contradiction_after_a_have.c
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
verifying "preserve_arm_contradiction_after_a_have.c";

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
        decreases n - i;
        owns l: list_at(node);
        invariant i >= 0;
        invariant i <= n;
        invariant node != 0;

        initialize by simp;
        preserve by {
            match l.model {
                CellList::Nil => {
                    have n >= 0 by { simp(); }
                    contradiction(l.model == CellList::Nil);
                },
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
