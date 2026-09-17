# one arm publication point per frontier

Selection, refutation, the cells the surviving arms agree on, and the naming of
the cells an `unfold` exposes are one mechanism. It runs at the eight frontiers
a proof passes through, listed in `docs/concepts/resources.md`, and each of
them decides from its own premises. This file states the same refutation at
every one of them over one resource, so a site that stops publishing fails here
rather than being found by the next proof shape that needs it.

`counted`'s `Count::Zero` arm states `fact n == 0`, so any premise that forces
`n` away from zero refutes it. `Count::Many` is then the one arm left, and
because it carries no fields the model has only one value: the equation itself
is published, which is what grants the arm's cells and lets `unfold` and proof
`match` name the constructor.

```c filename=arm_publication_sites.c
struct cell {
    int32 value;
    struct cell* next;
};

int32 entry_lowering(struct cell *node, int32 n) {
    return 0;
}

int32 unfold_site(struct cell *node, int32 n) {
    return node->value;
}

void loop_head(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        node->value = 7;
        i = i + 1;
    }
}

void loop_exit(struct cell *node, int32 n) {
    int32 i;
    int32 t;
    i = 0;
    t = 0;
    while (i < n) {
        t = 1;
    }
}

void contract_return(struct cell *node, int32 n) {
    int32 t;
    t = n;
}

void back_edge(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}

void case_split(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}

void guard_conjunct(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (n != 0 && node->value < 5) {
        i = 1;
    }
}
```

```click
verifying "arm_publication_sites.c";

spec enum Count {
    Zero,
    Many,
}

resource counted(p: struct cell*, n: int32) {
    field model: Count;
    match model {
        Count::Zero => { fact n == 0; },
        Count::Many => { owns p->value; owns p->next; fact n != 0; },
    }
}

int32 entry_lowering(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n > 0;
    ensures c.model == Count::Many;
} by {
    execute();
    simp();
}

int32 unfold_site(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n > 0;
    ensures c.model == Count::Many;
} by {
    unfold(c);
    execute();
    let c = fold(counted(node, n), { model: Count::Many }, {});
    simp();
}

void loop_head(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n > 0;
    requires n <= 1000;
} by {
    step();
    step();
    loop {
        owns c: counted(node, n);
        invariant i >= 0;
        invariant i <= n;
        invariant n > 0;

        initialize by simp;
        preserve by {
            match c.model {
                Count::Zero => { contradiction(c.model == Count::Zero); },
                Count::Many => {
                    unfold(c);
                    step();
                    step();
                    let c = fold(counted(node, n), { model: Count::Many }, {});
                    close_invariants();
                },
            }
        }
    }
    execute();
    simp();
}

void loop_exit(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n >= 0;
    requires n <= 1000;
    ensures c.model == Count::Zero;
} by {
    step();
    step();
    step();
    step();
    loop {
        owns c: counted(node, n);
        invariant i == 0;
        invariant n >= 0;

        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}

void contract_return(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires c.model != Count::Zero;
    owns node->next->value;
} by {
    execute();
    simp();
}

void back_edge(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n > 0;
    requires n <= 1000;
} by {
    step();
    step();
    loop {
        owns c: counted(node, n);
        invariant i >= 0;
        invariant i <= n;
        invariant n > 0;
        invariant c.model != Count::Zero;

        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}

void case_split(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n > 0;
    requires n <= 1000;
} by {
    step();
    step();
    loop {
        owns c: counted(node, n);
        invariant i >= 0;
        invariant i <= n;
        invariant n > 0;

        initialize by simp;
        preserve by {
            step();
            match c.model {
                Count::Zero => { contradiction(c.model == Count::Zero); },
                Count::Many => { close_invariants(); },
            }
        }
    }
    execute();
    simp();
}

void guard_conjunct(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n != 0;
} by {
    step();
    step();
    loop {
        owns c: counted(node, n);
        invariant n != 0;

        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```termination
pending: unranked loop
```

```expect
pass
```
