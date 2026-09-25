# A call's footprint includes the nodes of a recursive list it owns

`overwrite` owns `l: list_at(p)`, a recursive list whose `Cons` arm names a
`tail` child, and stores `1` in the head node. The caller stores `0`, calls
`overwrite`, and carries the `0` across the call with `transport`, which
would prove the false `result == 0`.

The footprint used to be enumerated by opening each held instance one body
layer, and a recursive, matched body with a child could not be opened, so
the list contributed nothing. A recursive family's footprint is now every
cell no other rule keeps -- its nodes past the argument are at addresses no
clause names -- and the transport has no frame evidence.

```c filename=call_through_recursive_list_footprint_includes_its_nodes.c
struct cell {
    int32 value;
    struct cell* next;
};

void overwrite(struct cell* p) {
    p->value = 1;
}

int32 caller(struct cell* p) {
    p->value = 0;
    overwrite(p);
    return p->value;
}
```

```click
verifying "call_through_recursive_list_footprint_includes_its_nodes.c";

spec enum CellList {
    Nil,
    Cons(struct cell*, int32, CellList),
}

resource list_at(p: struct cell*) {
    field model: CellList;
    match model {
        CellList::Nil => { fact p == 0; },
        CellList::Cons(identity, value, tail_model) => {
            owns p->value;
            owns &p->next;
            owns tail: list_at(p->next);
            fact p != 0;
            fact p == identity;
            fact tail.model == tail_model;
        },
    }
}

void overwrite(struct cell* p) {
    owns l: list_at(p);
    requires l.model != CellList::Nil;
    ensures l.model != CellList::Nil;
} by {
    match l.model {
        CellList::Nil => { contradiction(l.model == CellList::Nil); },
        CellList::Cons(identity, value, tail_model) => {
            let { tail: t } = unfold(l);
            execute();
            let l = fold(list_at(p), {
                model: CellList::Cons(identity, 1, tail_model)
            }, { tail: t });
            simp();
        },
    }
}

int32 caller(struct cell* p) {
    owns l: list_at(p);
    requires l.model != CellList::Nil;
    ensures result == 0;
} by {
    match l.model {
        CellList::Nil => { contradiction(l.model == CellList::Nil); },
        CellList::Cons(identity, value, tail_model) => {
            let { tail: t } = unfold(l);
            step();
            have p->value == 0 by simp;
            let l = fold(list_at(p), {
                model: CellList::Cons(identity, 0, tail_model)
            }, { tail: t });
            mark before;
            step(overwrite(p), { l: l });
            match l.model {
                CellList::Nil => { contradiction(l.model == CellList::Nil); },
                CellList::Cons(identity2, value2, tail_model2) => {
                    let { tail: t2 } = unfold(l);
                    have p->value == at(before, p->value) by {
                        transport(
                            at(before, p->value) == at(before, p->value),
                            p->value == at(before, p->value)
                        ) using { };
                    }
                    have p->value == 0 by simp;
                    step();
                    let l = fold(list_at(p), {
                        model: CellList::Cons(identity2, value2, tail_model2)
                    }, { tail: t2 });
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
