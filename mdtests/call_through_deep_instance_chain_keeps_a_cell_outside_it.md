# A call through a deep instance chain keeps a cell the chain does not own

The positive control of
[`call_through_deep_instance_chain_footprint_includes_its_memory.md`](call_through_deep_instance_chain_footprint_includes_its_memory.md).
The same ten-layer chain owns only `p->value`, and `overwrite` holds it and
writes that cell. The caller also owns `p->other` through `other1(p)`, an
instance with a named child, which it folds before the call. It carries
`p->other` across the call with `transport`.

A callee that owns `layer9(p)` may write `p->value` whether or not its body
does, so no transport of `p->value` across such a call can be valid; the
control is a cell outside the chain. The caller's folded `other1` keeps
nothing (what the caller keeps owning is opened one layer, and a body with a
child is not opened), so the cell survives only because the footprint is
exact: derived from the definitions it is `p->value` alone, which a constant
offset places apart from `p->other`. A footprint that summarized the chain as
unnamed memory would drop the cell.

```c filename=call_through_deep_instance_chain_keeps_a_cell_outside_it.c
struct node {
    int32 value;
    int32 other;
};

void overwrite(struct node* p) {
    p->value = 1;
}

int32 caller(struct node* p) {
    int32 before = p->other;
    overwrite(p);
    int32 after = p->other;
    return after == before;
}
```

```click
resource layer0(p: struct node*) {
    field tag: int32;
    owns p->value;
}

resource layer1(p: struct node*) {
    field tag: int32;
    owns child: layer0(p);
    fact child.tag == tag;
}

resource layer2(p: struct node*) {
    field tag: int32;
    owns child: layer1(p);
    fact child.tag == tag;
}

resource layer3(p: struct node*) {
    field tag: int32;
    owns child: layer2(p);
    fact child.tag == tag;
}

resource layer4(p: struct node*) {
    field tag: int32;
    owns child: layer3(p);
    fact child.tag == tag;
}

resource layer5(p: struct node*) {
    field tag: int32;
    owns child: layer4(p);
    fact child.tag == tag;
}

resource layer6(p: struct node*) {
    field tag: int32;
    owns child: layer5(p);
    fact child.tag == tag;
}

resource layer7(p: struct node*) {
    field tag: int32;
    owns child: layer6(p);
    fact child.tag == tag;
}

resource layer8(p: struct node*) {
    field tag: int32;
    owns child: layer7(p);
    fact child.tag == tag;
}

resource layer9(p: struct node*) {
    field tag: int32;
    owns child: layer8(p);
    fact child.tag == tag;
}

resource other0(p: struct node*) {
    field tag: int32;
    owns p->other;
}

resource other1(p: struct node*) {
    field tag: int32;
    owns child: other0(p);
    fact child.tag == tag;
}

verifying "call_through_deep_instance_chain_keeps_a_cell_outside_it.c";

void overwrite(struct node* p) {
    owns w: layer9(p);
    ensures w.tag == old(w.tag);
} by {
    let { tag: t9, child: c8 } = unfold(w);
    let { tag: t8, child: c7 } = unfold(c8);
    let { tag: t7, child: c6 } = unfold(c7);
    let { tag: t6, child: c5 } = unfold(c6);
    let { tag: t5, child: c4 } = unfold(c5);
    let { tag: t4, child: c3 } = unfold(c4);
    let { tag: t3, child: c2 } = unfold(c3);
    let { tag: t2, child: c1 } = unfold(c2);
    let { tag: t1, child: c0 } = unfold(c1);
    let { tag: t0 } = unfold(c0);
    execute();
    let c0 = fold(layer0(p), { tag: t0 }, {});
    let c1 = fold(layer1(p), { tag: t1 }, { child: c0 });
    let c2 = fold(layer2(p), { tag: t2 }, { child: c1 });
    let c3 = fold(layer3(p), { tag: t3 }, { child: c2 });
    let c4 = fold(layer4(p), { tag: t4 }, { child: c3 });
    let c5 = fold(layer5(p), { tag: t5 }, { child: c4 });
    let c6 = fold(layer6(p), { tag: t6 }, { child: c5 });
    let c7 = fold(layer7(p), { tag: t7 }, { child: c6 });
    let c8 = fold(layer8(p), { tag: t8 }, { child: c7 });
    let w = fold(layer9(p), { tag: t9 }, { child: c8 });
    simp();
}

int32 caller(struct node* p) {
    owns w: layer9(p);
    owns o: other1(p);
    ensures result == 1;
} by {
    let { tag: ot1, child: oc0 } = unfold(o);
    let { tag: ot0 } = unfold(oc0);
    step();
    step();
    let oc0 = fold(other0(p), { tag: ot0 }, {});
    let o = fold(other1(p), { tag: ot1 }, { child: oc0 });
    mark before;
    step(overwrite(p), { w: w });
    have p->other == at(before, p->other) by {
        transport(
            at(before, p->other) == at(before, p->other),
            p->other == at(before, p->other)
        ) using { };
    }
    let { tag: rt1, child: rc0 } = unfold(o);
    let { tag: rt0 } = unfold(rc0);
    step();
    step();
    let rc0 = fold(other0(p), { tag: rt0 }, {});
    let o = fold(other1(p), { tag: rt1 }, { child: rc0 });
    execute();
    simp();
}
```

```expect
pass
```
