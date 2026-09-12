# A loop holds a modeled instance across its iterations

The loop header binds the enclosing instance with the contract binder syntax,
`owns c: cell(node);`. The body then holds `c`, the invariants read `c.model`,
and the enclosing proof continues with `c` after the loop. The model here is
a matched one, so the loop carries a resource whose memory body depends on its
constructor without opening it: `requires c.model != Maybe::None` selects the
one arm that owns `node->value`, which is what the return reads after the
loop.

```c filename=loop_owns_modeled_instance.c
struct cell { int32 value; };

int32 spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return node->value;
}
```

```click
verifying "loop_owns_modeled_instance.c";

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

        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
