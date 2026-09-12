# A requirement selects a matched arm at contract lowering

A resource whose body is `match model { ... }` decides which cells it owns
from its model field, and a contract is lowered before any proof step runs.
The requirements of the section decide the arm instead: `c.model !=
Maybe::None` leaves `Maybe::Some` as the only possibility on a
two-constructor model, so the `Some` arm's cells are readable while the
instance stays folded, and `requires node->value >= 0` can read `node->value`.

Nothing is unfolded and no proof by cases happens: this is the same decision
the guard of an `if`-bodied resource already gets, made for a constructor
instead of a condition.

```c filename=armlower.c
struct cell { int32 value; };
int32 read_cell(struct cell *node) { return node->value; }
```

```click
verifying "armlower.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

int32 read_cell(struct cell* node) {
    owns c: cell(node);
    requires c.model != Maybe::None;
    requires node->value >= 0;
    ensures result >= 0;
} by {
    match c.model {
        Maybe::None => { contradiction(c.model == Maybe::None); },
        Maybe::Some(value) => {
            unfold(c);
            execute();
            let c = fold(cell(node), { model: Maybe::Some(value) });
            simp();
        },
    }
}
```

```expect
pass
```
