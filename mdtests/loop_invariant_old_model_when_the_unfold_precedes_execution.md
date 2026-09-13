# `old(name.field)` when the unfold precedes the first `step()`

A proof may open a modelled instance before it takes any C step: the first
statement's load is a cell of the instance's own arm, so the unfold has to come
first. The C execution then starts from a state that does not hold the
instance at all, and the refold leaves a later generation of it there.

Neither changes what `old(c.model)` means. It is the function-entry model of
the function's own binder of that name, and a loop whose invariant carries it
lowers that invariant against the contract's checked entry state, not against
the state the frontier happened to start from. A frontier loop used to read
the execution-start state, which here holds no `c` at all, and refused the
invariant with `the kernel lowering hit Paths`.

`d` is never unfolded, and `old(d.model)` in the same invariant always lowered:
it is the focused instance, not `old` itself, that the execution-start reading
lost.

```c filename=loop_invariant_old_model_when_the_unfold_precedes_execution.c
struct cell { int value; };

int spin(struct cell *node, struct cell *other, int n)
{
    int seen;
    int i;
    seen = node->value;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return seen;
}
```

```click
verifying "loop_invariant_old_model_when_the_unfold_precedes_execution.c";

spec enum Maybe { None, Some(int) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

int spin(struct cell* node, struct cell* other, int n) {
    requires n >= 0;
    owns c: cell(node);
    owns d: cell(other);
    requires c.model == Maybe::Some(7);
    ensures c.model == old(c.model);
    ensures d.model == old(d.model);
} by {
    unfold(c);
    step();
    let c = fold(cell(node), { model: Maybe::Some(7) });
    step();
    step();
    step();
    loop {
        owns c: cell(node);
        owns d: cell(other);
        invariant i >= 0;
        invariant i <= n;
        invariant c.model == old(c.model);
        invariant d.model == old(d.model);
    }
    execute();
    simp();
}
```

```expect
pass
```
