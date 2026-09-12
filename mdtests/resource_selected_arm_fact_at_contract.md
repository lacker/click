# a selected arm supplies its facts, not only its cells

`mdtests/resource_match_arm_selected_at_contract.md` shows the arm a section's
requirements select publishing its cells, so `requires node->value >= 0` can
read through a folded instance. This is the other half of that decision: the
arm also supplies what it says about them. `c.model != Maybe::None` selects the
`Some` arm, whose `fact p != 0` is then an entry premise, so `step()` decides
the guard of `if (node == 0)` instead of needing a `branch` whose then arm
unfolds and is infeasible.

A fact that names one of the arm's constructor bindings stays unpublished: the
binding is an unknown of the arm, and only `unfold` or a proof `match` names
it. `fact p->value == value` therefore does not travel, while `fact p != 0`
does.

Contract certification derives the same facts at its own entry state rather
than accepting them from the checked execution, so the two contexts agree.

```c filename=resource_selected_arm_fact_at_contract.c
struct cell { int32 value; };

int32 read_cell(struct cell *node) {
    if (node == 0) {
        return 0;
    }
    return node->value;
}
```

```click
verifying "resource_selected_arm_fact_at_contract.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p != 0; fact p->value == value; },
    }
}

int32 read_cell(struct cell* node) {
    owns c: cell(node);
    requires c.model != Maybe::None;
    requires node->value >= 0;
    ensures result >= 0;
} by {
    match c.model {
        Maybe::Some(value) => {
            step();
            unfold(c);
            execute();
            let c = fold(cell(node), { model: Maybe::Some(value) });
            simp();
        },
        Maybe::None => { contradiction(c.model == Maybe::None); },
    }
}
```

```expect
pass
```
