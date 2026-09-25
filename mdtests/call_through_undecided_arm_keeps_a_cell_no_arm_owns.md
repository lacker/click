# A call through an undecided matched arm keeps a cell no arm owns

The caller holds `s: slot_at(p)` without knowing its arm and passes it to
`overwrite`, which matches on the model and stores `1` in `p->value`. The
caller also owns `p->spare` through `spare1(p)`, an instance with a named
child, folded before the call, and carries `p->spare` across the call with
`transport`.

A matched body whose arm the call site does not decide contributes the union
of its arms: `Empty`'s `p->value` and `p->other`, and `Full`'s `p->value`
and, through its `rest` child, `p->other`. No arm owns `p->spare`, and a
constant offset places it apart from every one of those cells, so it keeps
its value. The caller's folded `spare1` keeps nothing on its own (a body
with a child is not opened by what the caller keeps owning), so the cell
survives only because the union is exact.

```c filename=call_through_undecided_arm_keeps_a_cell_no_arm_owns.c
struct node {
    int32 value;
    int32 other;
    int32 spare;
};

void overwrite(struct node* p) {
    p->value = 1;
}

int32 caller(struct node* p) {
    int32 before = p->spare;
    overwrite(p);
    int32 after = p->spare;
    return after == before;
}
```

```click
verifying "call_through_undecided_arm_keeps_a_cell_no_arm_owns.c";

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

resource spare0(p: struct node*) {
    field tag: int32;
    owns p->spare;
}

resource spare1(p: struct node*) {
    field tag: int32;
    owns child: spare0(p);
    fact child.tag == tag;
}

void overwrite(struct node* p) {
    owns s: slot_at(p);
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
    owns o: spare1(p);
    ensures result == 1;
} by {
    let { tag: ot1, child: oc0 } = unfold(o);
    let { tag: ot0 } = unfold(oc0);
    step();
    step();
    let oc0 = fold(spare0(p), { tag: ot0 }, {});
    let o = fold(spare1(p), { tag: ot1 }, { child: oc0 });
    mark before;
    step(overwrite(p), { s: s });
    have p->spare == at(before, p->spare) by {
        transport(
            at(before, p->spare) == at(before, p->spare),
            p->spare == at(before, p->spare)
        ) using { };
    }
    let { tag: rt1, child: rc0 } = unfold(o);
    let { tag: rt0 } = unfold(rc0);
    step();
    step();
    let rc0 = fold(spare0(p), { tag: rt0 }, {});
    let o = fold(spare1(p), { tag: rt1 }, { child: rc0 });
    execute();
    simp();
}
```

```expect
pass
```
