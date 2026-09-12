# A model's pointer payload is not equal to a pointer proved different

The companion to
[model_identity_pointer_payload](model_identity_pointer_payload.md). The
payload `identity` is the address the resource owns, so equating it with a
pointer the contract has already required to be different is false, and the
`have` that claims it has to be refused rather than lowered into some other
sort where the two addresses could be confused.

```c filename=pointer_payload_other.c
struct cell {
    int value;
};

int cell_same(struct cell *p, struct cell *q) {
    if (p == q) {
        return 1;
    }
    return 0;
}
```

```click
verifying "pointer_payload_other.c";

spec enum CellModel {
    Missing,
    Present(struct cell*, int),
}

resource cell_at(p: struct cell*) {
    field model: CellModel;
    match model {
        CellModel::Missing => { fact p == 0; },
        CellModel::Present(identity, value) => {
            owns p->value;
            fact p != 0;
            fact p == identity;
            fact p->value == value;
        },
    }
}

int cell_same(struct cell* p, struct cell* q) {
    owns c: cell_at(p);
    requires c.model != CellModel::Missing;
    requires p != q;
    ensures c.model == old(c.model);
} by {
    match c.model {
        CellModel::Missing => { contradiction(c.model == CellModel::Missing); },
        CellModel::Present(identity, value) => {
            unfold(c);
            have identity == q by { simp(); }
            execute();
            let c = fold(cell_at(p), { model: old(c.model) });
            simp();
        },
    }
}
```

```expect
fail: `have` failed: missing pure fact: pointer equality is true
```

The refusal is a proof failure over pointer equalities, not a lowering
failure: the proposition does lower, on one path, to the pointer equality the
resource's `fact p == identity` and the contract's `p != q` together refute.
