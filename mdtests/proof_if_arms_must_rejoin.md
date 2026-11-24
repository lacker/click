# A proof `if` whose arms end in different states does not rejoin

The `then` arm unfolds the slot and leaves it open; the `else` arm does not.
Both arms are still live at the same statement, but they hold different
resources, so there is no one state to continue from. Tactics written after
a proof `if` are checked once, so this is refused instead of running them
once per arm. `if P ensuring { ... } then { ... } else { ... }` is how arms
that end apart say what they agree on
([`proof_if_ensuring_rejoins.md`](proof_if_ensuring_rejoins.md)).

```c filename=proof_if_arms_must_rejoin.c
struct cell { int32 value; };

int32 peek(struct cell *node, int32 x) {
    int32 a;
    a = 0;
    return a;
}
```

```click
verifying "proof_if_arms_must_rejoin.c";

resource slot(p: struct cell*) {
    field model: int32;
    owns p->value;
    fact p->value == model;
}

int32 peek(struct cell* node, int32 x) {
    requires node != 0;
    owns c: slot(node);
    ensures result == 0;
} by {
    step();
    if x <= 0 {
        unfold(c);
    } else {
        have x > 0;
    }
    step();
    step();
    close();
}
```

```expect
fail: the arms of this proof `if` do not rejoin: with tactics written after the `if`
```
