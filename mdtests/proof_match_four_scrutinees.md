# Four nested proof `match` scrutinees

Nothing about the number of nested scrutinees is special-cased. This proof
opens four instances in turn — the shape C4's `rb_replace_node` needs, where
the subtree, both of its children, and the frame above it each have to be
matched before the body runs — and each arm costs its own region and nothing
more.

[`proof_match_four_constructors.md`](proof_match_four_constructors.md) is the
width of one match; this is the depth of four. The bound that remains is
[`proof_match_nesting_bound_named.md`](proof_match_nesting_bound_named.md).

```c filename=proof_match_four_scrutinees.c
struct cell { int32 value; };

int32 sum4(struct cell *a, struct cell *b, struct cell *c, struct cell *d) {
    return a->value + b->value + c->value + d->value;
}
```

```click
verifying "proof_match_four_scrutinees.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

int32 sum4(struct cell* a, struct cell* b, struct cell* c, struct cell* d) {
    owns ta: cell(a);
    owns tb: cell(b);
    owns tc: cell(c);
    owns td: cell(d);
    requires ta.model != Maybe::None;
    requires tb.model != Maybe::None;
    requires tc.model != Maybe::None;
    requires td.model != Maybe::None;
    requires a->value == 0;
    requires b->value == 0;
    requires c->value == 0;
    requires d->value == 0;
    ensures result == 0;
    ensures ta.model == old(ta.model);
} by {
    match ta.model {
        Maybe::None => { contradiction(ta.model == Maybe::None); },
        Maybe::Some(va) => {
            match tb.model {
                Maybe::None => { contradiction(tb.model == Maybe::None); },
                Maybe::Some(vb) => {
                    match tc.model {
                        Maybe::None => { contradiction(tc.model == Maybe::None); },
                        Maybe::Some(vc) => {
                            match td.model {
                                Maybe::None => { contradiction(td.model == Maybe::None); },
                                Maybe::Some(vd) => {
                                    unfold(ta);
                                    unfold(tb);
                                    unfold(tc);
                                    unfold(td);
                                    execute();
                                    let ta = fold(cell(a), { model: old(ta.model) }, {});
                                    let tb = fold(cell(b), { model: old(tb.model) }, {});
                                    let tc = fold(cell(c), { model: old(tc.model) }, {});
                                    let td = fold(cell(d), { model: old(td.model) }, {});
                                    simp();
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}
```

```expect
pass
```
