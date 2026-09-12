# a loop-body proof `match` must still cover every constructor

Running at a loop-body frontier changes where a proof `match` may appear, not
what it must prove. The case split is exhaustive only if every constructor has
an arm, so a `preserve` body that handles one of two constructors is refused
the same way a function-entry `match` is.

```c filename=loop_body_proof_match_missing_arm.c
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
verifying "loop_body_proof_match_missing_arm.c";

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
fail: proof `match` must cover every constructor exactly once
```
