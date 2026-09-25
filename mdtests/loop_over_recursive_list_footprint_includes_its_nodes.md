# A loop's footprint includes the nodes of a recursive list it owns

`overwrite_head` stores `5` in the first node of a list, then runs a loop
that owns `l: list_at(node)` and stores `7` in the same cell at least once
(`n >= 1`). After the loop the proof carries the `5` across it with
`transport` and returns the cell, which would prove the false
`result == 5`.

A loop that declares a resource havocs the memory the resource owns.
`list_at` is recursive: its `Cons` arm names a `tail: list_at(p->next)`
child. That footprint used to be enumerated by opening the instance one body
layer, and an instance with a named child, a matched body whose arm was not
decided, or a recursive body could not be opened, so it contributed nothing
and the loop was summarized as writing none of the list. A recursive family
owns one set of cells per node, however many nodes are live, at addresses no
argument spells, so its footprint is now every cell no other rule keeps, and
the transport has no frame evidence.

```c filename=loop_over_recursive_list_footprint_includes_its_nodes.c
struct cell {
    int32 value;
    struct cell* next;
};

int32 overwrite_head(struct cell *node, int32 n) {
    int32 i;
    node->value = 5;
    i = 0;
    while (i < n) {
        node->value = 7;
        i = i + 1;
    }
    return node->value;
}
```

```click
verifying "loop_over_recursive_list_footprint_includes_its_nodes.c";

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

int32 overwrite_head(struct cell* node, int32 n) {
    requires n >= 1;
    requires n <= 1000;
    requires node != 0;
    owns l: list_at(node);
    requires list_head_is(l.model, node) == 1;
    ensures result == 5;
} by {
    match l.model {
        CellList::Nil => { contradiction(l.model == CellList::Nil); },
        CellList::Cons(identity0, value0, tail_model0) => {
            let { tail: t0 } = unfold(l);
            step();
            step();
            have node->value == 5 by simp;
            have list_head_is(CellList::Cons(node, 5, tail_model0), node) == 1 by {
                unfold(list_head_is(CellList::Cons(node, 5, tail_model0), node));
            }
            let l = fold(list_at(node), {
                model: CellList::Cons(node, 5, tail_model0)
            }, { tail: t0 });
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
            match l.model {
                CellList::Nil => { contradiction(l.model == CellList::Nil); },
                CellList::Cons(identity, value, tail_model) => {
                    let { tail: t } = unfold(l);
                    have node->value == at(pre, node->value) by {
                        transport(
                            at(pre, node->value) == at(pre, node->value),
                            node->value == at(pre, node->value)
                        ) using { };
                    }
                    have at(pre, node->value) == 5 by simp;
                    have node->value == 5 by {
                        rewrite(node->value == at(pre, node->value));
                        assumption();
                    }
                    step();
                    let l = fold(list_at(node), {
                        model: CellList::Cons(node, 5, tail_model)
                    }, { tail: t });
                    simp();
                },
            }
        },
    }
}
```

```expect
fail: `transport using` found no frame evidence
```
