# `old(name.field)` in a loop invariant is the function-entry instance

`old(c.model)` in a loop invariant means the function-entry model of the
function's own binder of that name, whatever the proof did to the instance
before the loop. A body that opened and refolded the binder first broke that:
the lowering looked the instance up in the state it was handed, found the
refolded generation with a concrete model instead of the entry's symbolic one,
and refused the invariant.

An `at(...)` snapshot still names a state, so an instance it does not hold is
still an error there. The function entry is not such a name: its value always
has the kernel's own entry projection, which is what `old(...)` now lowers to.

```c filename=loop_invariant_old_model_after_refold.c
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
verifying "loop_invariant_old_model_after_refold.c";

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
    requires c.model == Maybe::Some(7);
    ensures c.model == old(c.model);
} by {
    unfold(c);
    let c = fold(cell(node), { model: Maybe::Some(7) });
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
