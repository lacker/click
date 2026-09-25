# A loop over a recursive list keeps the cells the function keeps owning

The positive control of
[`loop_over_recursive_list_footprint_includes_its_nodes.md`](loop_over_recursive_list_footprint_includes_its_nodes.md).
The loop owns the same recursive `list_at(node)`, whose footprint is every
cell no other rule keeps. The function also owns `flag[0..1]`, outside the
loop's declaration, and carries `flag[0] == 5` across the loop with
`transport`.

A declaring loop's body holds only its declared resources and views of the
rest, and a store needs ownership, so the loop cannot write a cell the
function keeps owning outside the declaration. The loop head keeps such a
cell whatever the footprint covers, which is what makes a footprint of
unnamed memory usable.

```c filename=loop_over_recursive_list_keeps_cells_the_function_keeps.c
struct cell {
    int32 value;
    struct cell* next;
};

int32 keep_flag(struct cell *node, int32 *flag, int32 n) {
    int32 i;
    flag[0] = 5;
    i = 0;
    while (i < n) {
        node->value = 7;
        i = i + 1;
    }
    return flag[0];
}
```

```click
verifying "loop_over_recursive_list_keeps_cells_the_function_keeps.c";

spec enum CellList {
    Nil,
    Cons(struct cell*, int32, CellList),
}

function list_head_is(xs: CellList, p: struct cell*) -> int32 {
    match xs {
        CellList::Nil => if p == 0 { 1 } else { 0 },
        CellList::Cons(identity, value, tail_model) =>
            if identity == p { 1 } else { 0 },
    }
}

resource list_at(p: struct cell*) {
    field model: CellList;
    match model {
        CellList::Nil => { },
        CellList::Cons(identity, value, tail_model) => {
            owns p->value;
            owns &p->next;
            owns tail: list_at(p->next);
            fact p == identity;
            fact p->value == value;
            fact tail.model == tail_model;
        },
    }
}

int32 keep_flag(struct cell* node, int32* flag, int32 n) {
    owns flag[0..1];
    requires n >= 1;
    requires n <= 1000;
    requires node != 0;
    owns l: list_at(node);
    requires list_head_is(l.model, node) == 1;
    ensures result == 5;
} by {
    step();
    step();
    have flag[0] == 5 by simp;
    mark pre;
    step();
    loop {
        owns l: list_at(node);
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        invariant node != 0;
        invariant list_head_is(l.model, node) == 1;

        initialize by simp;
        preserve by {
            match l.model {
                CellList::Nil => { contradiction(l.model == CellList::Nil); },
                CellList::Cons(identity, value, tail_model) => {
                    have 0 <= n - i - 1 by { arithmetic() using { i < n; i >= 0; n >= 1; } }
                    have n - i - 1 < n - i by { arithmetic() using { i < n; i >= 0; n >= 1; } }
                    let { tail: t } = unfold(l);
                    have list_head_is(CellList::Cons(node, 7, tail_model), node) == 1 by {
                        unfold(list_head_is(CellList::Cons(node, 7, tail_model), node));
                    }
                    step();
                    step();
                    let l = fold(list_at(node), {
                        model: CellList::Cons(node, 7, tail_model)
                    }, { tail: t });
                    close_invariants();
                },
            }
        }
    }
    have flag[0] == at(pre, flag[0]) by {
        transport(
            at(pre, flag[0]) == at(pre, flag[0]),
            flag[0] == at(pre, flag[0])
        ) using { };
    }
    have at(pre, flag[0]) == 5 by simp;
    have flag[0] == 5 by {
        rewrite(flag[0] == at(pre, flag[0]));
        assumption();
    }
    execute();
    simp();
}
```

```expect
pass
```
