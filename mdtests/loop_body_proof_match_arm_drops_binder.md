# a loop-body `match` arm must restore the loop binder

Each arm of a proof `match` inside `preserve` reaches the loop's back edge on
its own path, so each arm must hand the loop binder back on its own. This
`Sign::Pos` arm unfolds the instance and never folds it again, so the back edge
finds no `cell` at the binder's arguments even though the sibling arm does.

```c filename=loop_body_proof_match_arm_drops_binder.c
struct cell { int32 value; };

void spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}
```

```click
verifying "loop_body_proof_match_arm_drops_binder.c";

spec enum Sign { Neg(int32), Pos(int32) }

resource cell(p: struct cell*) {
    field model: Sign;
    match model {
        Sign::Neg(value) => {
            owns p->value;
            fact p->value == value;
            fact value < 0;
        },
        Sign::Pos(value) => {
            owns p->value;
            fact p->value == value;
            fact value >= 0;
        },
    }
}

void spin(struct cell* node, int32 n) {
    requires n >= 0;
    requires node != 0;
    owns c: cell(node);
    ensures c.model == old(c.model);
} by {
    step();
    step();
    loop {
        owns c: cell(node);
        invariant i >= 0;
        invariant i <= n;
        invariant c.model == old(c.model);

        initialize by simp;
        preserve by {
            match c.model {
                Sign::Neg(value) => {
                    have Sign::Neg(value) == old(c.model) by {
                        simp() using { c.model == Sign::Neg(value); c.model == old(c.model); }
                    }
                    unfold(c);
                    step();
                    let c = fold(cell(node), { model: Sign::Neg(value) });
                    close_invariants();
                },
                Sign::Pos(value) => {
                    unfold(c);
                    step();
                    close_invariants();
                },
            }
        }
    }
    step();
    simp();
}
```

```expect
fail: loop binder `c` has no owned `cell` instance
```
