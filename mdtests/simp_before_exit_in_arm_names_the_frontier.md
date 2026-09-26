# `simp` before the function exit inside a proof `match` arm names the frontier

`simp` closes the outcome claims at function exit and does not execute. A
script that steps through every statement of a body still stands before the
body's end, one step short of the exit, and the arm driver used to decline
that shape with a generic "not implemented in this execution context". It
now says where the frontier is and how to reach the exit. The same script
with one more `step()`, or with `execute()` in place of the steps, verifies.

```c filename=simp_before_exit_in_arm_names_the_frontier.c
struct cell { int32 value; };

void bump(struct cell *node) {
    node->value = 1;
    node->value = 2;
}
```

```click
verifying "simp_before_exit_in_arm_names_the_frontier.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

void bump(struct cell* node) {
    requires node != 0;
    owns c: cell(node);
    requires c.model != Maybe::None;
    ensures c.model == Maybe::Some(2);
} by {
    match c.model {
        Maybe::None => { contradiction(c.model == Maybe::None); },
        Maybe::Some(value) => {
            unfold(c);
            step();
            step();
            let c = fold(cell(node), { model: Maybe::Some(2) });
            simp();
        },
    }
}
```

```expect
fail: the frontier is at statement 2, `return void`. Step to the exit first with `step()`
```
