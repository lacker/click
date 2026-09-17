# an arithmetic requirement refutes an arm at contract entry

Refutation reads a premise of whatever shape the exact checkers decide, and it
reads it the same way wherever an instance enters the premises. `requires
count > 0` is not a disequality and says nothing about a model directly, but
`counter`'s `Tally::Empty` arm states `fact count == 0`, and the checkers
decide `count != 0` from `count > 0`. So the arm goes, `Tally::Filled` is the
one left, and because it carries no fields the model has only one value.

This used to hold at a loop head and not at a contract, because contract entry
lowering published the selected arm's cells and facts but never ran refutation
at all. Both functions below state the same thing about the same resource: the
first from a requirement, the second from the invariant that repeats it. One
publication point decides both.

```c filename=contract_arithmetic_refutes_an_arm.c
struct box {
    int32 value;
};

int32 from_requirement(struct box *b, int32 count) {
    return 0;
}

void from_invariant(struct box *b, int32 count) {
    int32 i;
    i = 0;
    while (i < count) {
        i = i + 1;
    }
}
```

```click
verifying "contract_arithmetic_refutes_an_arm.c";

spec enum Tally {
    Empty,
    Filled,
}

resource counter(b: struct box*, count: int32) {
    field model: Tally;
    match model {
        Tally::Empty => { fact count == 0; },
        Tally::Filled => { owns b->value; fact count != 0; },
    }
}

int32 from_requirement(struct box* b, int32 count) {
    owns c: counter(b, count);
    requires count > 0;
    ensures c.model == Tally::Filled;
} by {
    execute();
    simp();
}

void from_invariant(struct box* b, int32 count) {
    owns c: counter(b, count);
    requires count > 0;
    requires count <= 1000;
} by {
    step();
    step();
    loop {
        decreases count - i;
        owns c: counter(b, count);
        invariant i >= 0;
        invariant i <= count;
        invariant count > 0;

        initialize by simp;
        preserve by {
            match c.model {
                Tally::Empty => { contradiction(c.model == Tally::Empty); },
                Tally::Filled => {
                    step();
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
