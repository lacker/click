# `auto` refuses a goal no rewrite chain closes

Rewriting `Walk::At(wd, rest)` to `c.model` leaves `black(c.model) == 0`,
which contradicts the requirement rather than following from it. No chain of
connected equalities closes the goal, so `auto` fails.

```c filename=auto_refuses_a_constructor_rewrite_that_does_not_close.c
void touch(int32 n) {
}
```

```click
verifying "auto_refuses_a_constructor_rewrite_that_does_not_close.c";

spec enum Walk { At(Integer, Walk), Done }

function black(w: Walk) -> int32 decreases w {
    match w { Walk::At(wd, rest) => black(rest), Walk::Done => 1 }
}

resource token(k: int32) {
    field model: Walk;
}

void touch(int32 n) {
    owns c: token(n);
    requires black(c.model) == 1;
    ensures 1 == 1;
} by {
    match c.model {
        Walk::At(wd, rest) => {
            have black(Walk::At(wd, rest)) == 0 by auto;
            step();
            step();
            simp();
        },
        Walk::Done => {
            step();
            step();
            simp();
        },
    }
}
```

```expect
fail: did not close its checked nested goal
```
