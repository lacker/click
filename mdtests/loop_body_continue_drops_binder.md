# A `continue` that does not hand its binder back is refused

The back edge's obligations are owed at a `continue` exactly as they are owed
at the body's end, and handing the loop's declared instance back is one of
them. This arm unfolds `c` and jumps to the back edge without refolding it, so
the loop head has no instance to bind `c` to on the next visit and the rule
refuses.

The positive is [`loop_body_proof_match.md`](loop_body_proof_match.md), whose
arm refolds `cell(node)` before it closes.

```c filename=continue_drops_binder.c
struct cell { int32 value; };

int32 spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
        continue;
    }
    return node->value;
}
```

```click
verifying "continue_drops_binder.c";

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
        invariant i <= n;
        invariant c.model == old(c.model);
        invariant c.model != Maybe::None;

        initialize by simp;
        preserve by {
            match c.model {
                Maybe::None => { contradiction(c.model == Maybe::None); },
                Maybe::Some(value) => {
                    have Maybe::Some(value) == old(c.model) by {
                        simp() using { c.model == Maybe::Some(value); c.model == old(c.model); }
                    }
                    unfold(c);
                    step();
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
