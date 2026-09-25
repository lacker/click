# A call's footprint includes a matched arm with a child

`slot_at(p)` matches on its model: `Empty` owns `p->value` and `p->other`,
and `Full(v)` owns `p->value` and names a `rest: other_at(p)` child.
`overwrite` holds the slot and stores `1` in `p->value` in either arm. The
caller, whose slot is `Full(3)`, stores `0`, calls `overwrite`, and carries
the `0` across the call with `transport`, which would prove the false
`result == 0`.

The footprint used to be enumerated by opening each held instance one body
layer, and an arm with a named child could not be opened that way, so the
slot contributed nothing. The footprint is now derived from the definitions:
the decided arm's clauses and its child are evaluated at the call, so the
havoc covers `p->value` and the transport has no frame evidence.

```c filename=call_through_matched_arm_child_footprint_includes_its_memory.c
struct node {
    int32 value;
    int32 other;
};

void overwrite(struct node* p) {
    p->value = 1;
}

int32 caller(struct node* p) {
    p->value = 0;
    overwrite(p);
    return p->value;
}
```

```click
verifying "call_through_matched_arm_child_footprint_includes_its_memory.c";

spec enum Slot {
    Empty,
    Full(int32),
}

resource other_at(p: struct node*) {
    field tag: int32;
    owns p->other;
}

resource slot_at(p: struct node*) {
    field model: Slot;
    match model {
        Slot::Empty => { owns p->value; owns p->other; },
        Slot::Full(v) => {
            owns p->value;
            owns rest: other_at(p);
            fact rest.tag == v;
        },
    }
}

void overwrite(struct node* p) {
    owns s: slot_at(p);
    ensures s.model == old(s.model);
} by {
    match s.model {
        Slot::Empty => {
            unfold(s);
            execute();
            let s = fold(slot_at(p), { model: Slot::Empty });
            simp();
        },
        Slot::Full(v) => {
            let { rest: r } = unfold(s);
            execute();
            let s = fold(slot_at(p), { model: Slot::Full(v) }, { rest: r });
            simp();
        },
    }
}

int32 caller(struct node* p) {
    owns s: slot_at(p);
    requires s.model == Slot::Full(3);
    ensures result == 0;
} by {
    let { rest: r } = unfold(s);
    step();
    have p->value == 0 by simp;
    let s = fold(slot_at(p), { model: Slot::Full(3) }, { rest: r });
    mark before;
    step(overwrite(p), { s: s });
    let { rest: r2 } = unfold(s);
    have p->value == at(before, p->value) by {
        transport(
            at(before, p->value) == at(before, p->value),
            p->value == at(before, p->value)
        ) using { };
    }
    step();
    let s = fold(slot_at(p), { model: Slot::Full(3) }, { rest: r2 });
    simp();
}
```

```expect
fail: `transport using` found no frame evidence
```
