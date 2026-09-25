# A call's footprint includes a cell ten instance layers below its resource

Ten field-bearing resources form a chain: `layer0(p)` owns `p->value`, and
each `layerN(p)` names `layerN-1(p)` as a child. `overwrite` holds `layer9(p)`
and stores `1` in `p->value`; its contract says nothing about the cell. The
caller stores `0`, calls `overwrite`, and tries to carry the `0` across the
call with `transport`, which would prove the false `p->value == 0`.

A call havocs the memory the callee's resources own. That footprint used to
be enumerated by opening each held instance one body layer, as `unfold`
does, and an instance with a named child could not be opened that way (nor
could one nested past eight layers), so it contributed nothing: the call was
summarized as writing none of the chain's memory and the transport
succeeded. The footprint is now derived from the definitions: each layer's
child is evaluated at the call and its clauses counted, one visit per layer,
so the havoc covers `p->value` and the transport has no frame evidence.

```c filename=call_through_deep_instance_chain_footprint_includes_its_memory.c
struct node {
    int32 value;
};

void overwrite(struct node* p) {
    p->value = 1;
}

void caller(struct node* p) {
    p->value = 0;
    overwrite(p);
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

verifying "call_through_deep_instance_chain_footprint_includes_its_memory.c";

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

void caller(struct node* p) {
    owns w: layer9(p);
    ensures p->value == 0;
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
    step();
    have p->value == 0 by simp;
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
    mark before;
    step(overwrite(p), { w: w });
    let { tag: at9, child: ac8 } = unfold(w);
    let { tag: at8, child: ac7 } = unfold(ac8);
    let { tag: at7, child: ac6 } = unfold(ac7);
    let { tag: at6, child: ac5 } = unfold(ac6);
    let { tag: at5, child: ac4 } = unfold(ac5);
    let { tag: at4, child: ac3 } = unfold(ac4);
    let { tag: at3, child: ac2 } = unfold(ac3);
    let { tag: at2, child: ac1 } = unfold(ac2);
    let { tag: at1, child: ac0 } = unfold(ac1);
    let { tag: at0 } = unfold(ac0);
    have p->value == at(before, p->value) by {
        transport(
            at(before, p->value) == at(before, p->value),
            p->value == at(before, p->value)
        ) using { };
    }
    let ac0 = fold(layer0(p), { tag: at0 }, {});
    let ac1 = fold(layer1(p), { tag: at1 }, { child: ac0 });
    let ac2 = fold(layer2(p), { tag: at2 }, { child: ac1 });
    let ac3 = fold(layer3(p), { tag: at3 }, { child: ac2 });
    let ac4 = fold(layer4(p), { tag: at4 }, { child: ac3 });
    let ac5 = fold(layer5(p), { tag: at5 }, { child: ac4 });
    let ac6 = fold(layer6(p), { tag: at6 }, { child: ac5 });
    let ac7 = fold(layer7(p), { tag: at7 }, { child: ac6 });
    let ac8 = fold(layer8(p), { tag: at8 }, { child: ac7 });
    let w = fold(layer9(p), { tag: at9 }, { child: ac8 });
    execute();
    simp();
}
```

```expect
fail: `transport using` found no frame evidence
```
