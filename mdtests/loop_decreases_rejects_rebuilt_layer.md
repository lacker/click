# Rebuilding the same recursive layer is not structural descent

The C is unchanged from `loop_decreases_rejects_same_instance.md`. Here the
measure is a recursive context. Each iteration unfolds its `Link`, exposing
`rest`, and then folds a new instance with that same `Link` model. The fresh
instance identity does not make it a strict descendant of the loop-head model.
The proof must reach the back-edge descent diagnostic after the fold succeeds.

The scalar counter makes the C loop terminate, but this sidecar deliberately
claims the wrong structural measure. Removing only `decreases c;` gives a
passing partial-correctness proof; the unchanged model cannot certify progress.

```c filename=loop_decreases_rejects_rebuilt_layer.c
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
verifying "loop_decreases_rejects_rebuilt_layer.c";

spec enum Context { Top, Link(Context) }

resource context() {
    field model: Context;
    match model {
        Context::Top => {},
        Context::Link(rest_model) => {
            owns rest: context();
            fact rest.model == rest_model;
        },
    }
}

void spin(struct cell* node, int32 n) {
    requires n >= 0;
    owns c: context();
    requires c.model == Context::Link(Context::Top);
    ensures c.model == old(c.model);
} by {
    step();
    step();
    loop {
        owns c: context();
        decreases c;
        invariant i >= 0;
        invariant i <= n;
        invariant c.model == Context::Link(Context::Top);

        initialize by simp;
        preserve by {
            unfold(c) as { rest: r };
            let rebuilt = fold(context(), {
                model: Context::Link(Context::Top)
            }, { rest: r });
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
