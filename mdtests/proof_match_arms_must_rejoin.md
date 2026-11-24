# A proof `match` whose arms end in different states does not rejoin

The `Neg` arm unfolds the cell and leaves it open; the `Pos` arm does not. The
arms end at the same program point but hold different resources, so there is
no one state to continue from. Tactics written after a `match` are checked
once, so this is refused instead of running them once per arm.

```c filename=proof_match_arms_must_rejoin.c
struct cell { int32 value; };

int32 peek(struct cell *node) {
    int32 a;
    a = 0;
    return a;
}
```

```click
verifying "proof_match_arms_must_rejoin.c";

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

int32 peek(struct cell* node) {
    requires node != 0;
    owns c: cell(node);
    ensures result == 0;
} by {
    step();
    match c.model {
        Sign::Neg(value) => {
            unfold(c);
        },
        Sign::Pos(value) => {
            have value < 0 or value >= 0;
        },
    }
    step();
    step();
    close();
}
```

```expect
fail: the arms of this proof `match` do not rejoin
```
