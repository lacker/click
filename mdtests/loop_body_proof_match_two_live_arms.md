# A loop-body proof `match` with two live arms

Neither constructor is excluded here, so the preservation region really splits:
each arm runs its own iteration, refolds its own instance, and closes the
invariants separately. The arms never rejoin — a preservation path does not
join across the back edge — so the loop rule is certified from two paths and
the preservation certificate is reassembled as the `match` that produced them.

```c filename=loop_body_proof_match_two_live_arms.c
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
verifying "loop_body_proof_match_two_live_arms.c";

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
                    have Sign::Pos(value) == old(c.model) by {
                        simp() using { c.model == Sign::Pos(value); c.model == old(c.model); }
                    }
                    unfold(c);
                    step();
                    let c = fold(cell(node), { model: Sign::Pos(value) });
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
pass
```
