# A `break` inside a proof `match` arm exits the loop

A proof `match` in `preserve` splits the body into one path per constructor,
and those paths are never joined: each reaches the loop's own boundary on its
own. A `break` is one of the ways to reach it. The live arm here leaves the
loop immediately, so it closes no invariant and hands its binder to nobody; it
becomes an exit of the loop at the state it left in, holding the loop's
declared instance, and the excluded arm is closed by `contradiction` as in
[`loop_body_proof_match.md`](loop_body_proof_match.md).

The exit therefore keeps the resource the loop declared, which is what lets
`spin` return `node->value` after the loop and satisfy a postcondition about
`c.model`.

```c filename=break_in_match_arm.c
struct cell { int32 value; };

int32 spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        break;
    }
    return node->value;
}
```

```click
verifying "break_in_match_arm.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

int32 spin(struct cell* node, int32 n) {
    requires n >= 0;
    requires node != 0;
    owns c: cell(node);
    requires c.model != Maybe::None;
    ensures c.model == old(c.model);
} by {
    step();
    step();
    loop {
        owns c: cell(node);
        invariant i >= 0;
        invariant c.model == old(c.model);
        invariant c.model != Maybe::None;

        initialize by simp;
        preserve by {
            match c.model {
                Maybe::None => { contradiction(c.model == Maybe::None); },
                Maybe::Some(value) => {
                    step();
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
