# a structural loop measure refuses a back edge that stays put

`decreases c;` on a loop names the loop's own resource binder, so the back
edge must hand back a direct contained child, in the exact resource
definition, of the instance `c` held at the loop head. This body keeps the
same instance, so the descent is refused by name.

```c filename=loop_decreases_rejects_same_instance.c
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
verifying "loop_decreases_rejects_same_instance.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

void spin(struct cell* node, int32 n) {
    requires n >= 0;
    requires node != 0;
    owns c: cell(node);
    requires c.model == Maybe::Some(7);
    ensures c.model == old(c.model);
} by {
    step();
    step();
    loop {
        owns c: cell(node);
        decreases c;
        invariant i >= 0;
        invariant i <= n;
        invariant c.model == Maybe::Some(7);

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
fail: does not descend
```
