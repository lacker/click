# A call's footprint includes memory a resource owns through a witness

`hop(p)` owns `object(p)` and, through an existential witness `next` that
`p->word` spells, the cell `next->value`. `holder(p, q)` contains `hop(p)`
and names a `side: tagged(q)` child. `overwrite` holds `holder(p, q)` and
stores `1` through the witness; its contract says nothing about the cell.
The caller stores `0` there, calls `overwrite`, and carries the `0` across
the call with `transport`, which would prove the false `result == 0`.

The footprint used to be enumerated by opening each held instance one body
layer, and `holder` names a child, so it could not be opened and
contributed nothing. The footprint is now derived from the definitions:
`holder`'s contained `hop(p)` is evaluated at the call, its witness bound as
`unfold` binds it, to the recorded origin of `p->word` (or else to a fresh
symbolic pointer, which no separation rule places apart from anything), so
the havoc covers `next->value` and the transport has no frame evidence.

```c filename=call_through_witness_footprint_includes_its_memory.c
struct node {
    int32 value;
    unsigned long word;
};

void overwrite(struct node* p, struct node* q) {
    struct node* next = (struct node*)(p->word & ~1);
    next->value = 1;
}

int32 caller(struct node* p, struct node* q) {
    struct node* next = (struct node*)(p->word & ~1);
    next->value = 0;
    overwrite(p, q);
    int32 seen = next->value;
    return seen;
}
```

```click
resource hop(node: struct node*) {
    owns object(node);
    let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
    owns next->value;
}

resource tagged(q: struct node*) {
    field tag: int32;
    owns q->value;
}

resource holder(p: struct node*, q: struct node*) {
    field tag: int32;
    owns side: tagged(q);
    fact side.tag == tag;
    contains hop(p);
}

verifying "call_through_witness_footprint_includes_its_memory.c";

void overwrite(struct node* p, struct node* q) {
    requires p != 0;
    owns h: holder(p, q);
    ensures h.tag == old(h.tag);
} by {
    let { tag: t, side: s } = unfold(h);
    unfold(hop(p));
    step();
    step();
    step();
    fold(hop(p));
    let h = fold(holder(p, q), { tag: t }, { side: s });
    execute();
    simp();
}

int32 caller(struct node* p, struct node* q) {
    requires p != 0;
    owns h: holder(p, q);
    ensures result == 0;
} by {
    let { tag: t, side: s } = unfold(h);
    unfold(hop(p));
    step();
    step();
    step();
    have next->value == 0 by simp;
    fold(hop(p));
    let h = fold(holder(p, q), { tag: t }, { side: s });
    mark before;
    step(overwrite(p, q), { h: h });
    let { tag: t2, side: s2 } = unfold(h);
    have next->value == at(before, next->value) by {
        transport(
            at(before, next->value) == at(before, next->value),
            next->value == at(before, next->value)
        ) using { };
    }
    have next->value == 0 by simp;
    unfold(hop(p));
    step();
    step();
    fold(hop(p));
    let h = fold(holder(p, q), { tag: t2 }, { side: s2 });
    execute();
    simp();
}
```

```expect
fail: `transport using` found no frame evidence
```
