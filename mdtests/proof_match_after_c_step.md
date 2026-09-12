# A proof `match` runs after a C step

A proof `match` is not restricted to unchanged function entry. The constructor
witnesses it introduces are fresh against the region this proof started in and
against everything the kernel has issued since, so the split is available at
any frontier the proof has reached — here, after one executed statement.

The constructor equation is a fact of this path from the split onwards, not an
entry assumption of the whole function, so certification does not
assume it as a requirement of the function.

```c filename=proof_match_after_c_step.c
struct cell { int32 value; };

int32 read_after_step(struct cell *node) {
    int32 i;
    i = 0;
    return node->value;
}
```

```click
verifying "proof_match_after_c_step.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

int32 read_after_step(struct cell* node) {
    requires node != 0;
    owns c: cell(node);
    requires c.model != Maybe::None;
    ensures c.model == old(c.model);
} by {
    step();
    match c.model {
        Maybe::None => { contradiction(c.model == Maybe::None); },
        Maybe::Some(value) => {
            unfold(c);
            execute();
            let c = fold(cell(node), { model: Maybe::Some(value) });
            have Maybe::Some(value) == old(c.model) by {
                simp() using { old(c.model) == Maybe::Some(value); }
            }
            simp();
        },
    }
}
```

```expect
pass
```
