# A loop-body proof `match` whose arms end apart may not share a continuation

Both arms of the `match` are live. Each opens its instance, runs the body,
and refolds with its own constructor, so the arms end at one program point
holding cells with different models. The tactics written after the `match`
would then be the rest of both arms' iterations, checked once per arm, and
every further split of this kind would double that again. That is refused.

The arms rejoin through an interface in
[`loop_body_proof_match_ensuring_rejoins.md`](loop_body_proof_match_ensuring_rejoins.md),
which is this proof with `ensuring { owns c: cell(node); }` on the `match`.

```c filename=loop_body_proof_match_shared_continuation.c
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
verifying "loop_body_proof_match_shared_continuation.c";

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
        decreases n - i;
        owns c: cell(node);
        invariant i >= 0;
        invariant i <= n;
        invariant c.model == old(c.model);

        initialize by close();
        maintain by {
            match c.model {
                Sign::Neg(value) => {
                    have Sign::Neg(value) == old(c.model) by {
                        close() using { c.model == Sign::Neg(value); c.model == old(c.model); };
                    }
                    unfold(c);
                    step();
                    let c = fold(cell(node), { model: Sign::Neg(value) });
                },
                Sign::Pos(value) => {
                    have Sign::Pos(value) == old(c.model) by {
                        close() using { c.model == Sign::Pos(value); c.model == old(c.model); };
                    }
                    unfold(c);
                    step();
                    let c = fold(cell(node), { model: Sign::Pos(value) });
                },
            }
            have i >= 0;
        }
    }
    step();
    close();
}
```

```expect
fail: are reached by more than one of its arms at the same program point
```
