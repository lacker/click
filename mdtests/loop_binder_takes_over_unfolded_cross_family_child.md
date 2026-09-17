# A loop binder can take over an unfolded cross-family child

An `unfold ... as` child initially carries its parent's family in parser state
because the selected resource arm is resolved later. A loop binder may reuse
that child name with its declared family; declaration expansion remains the
authority that checks the slot actually has that family.

```c filename=loop_binder_takes_over_unfolded_cross_family_child.c
void drain(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
}
```

```click
spec enum LeafModel { Unit }
spec enum RootModel { Has(LeafModel) }

resource leaf() {
    field model: LeafModel;
    match model {
        LeafModel::Unit => {},
    }
}

resource root() {
    field model: RootModel;
    match model {
        RootModel::Has(child_model) => {
            owns child: leaf();
            fact child.model == child_model;
        },
    }
}

verifying "loop_binder_takes_over_unfolded_cross_family_child.c";

void drain(int32 n) {
    consumes r: root();
    requires n >= 0;
    requires r.model == RootModel::Has(LeafModel::Unit);
    produces out: root();
} by {
    match r.model {
        RootModel::Has(child_model) => {
            unfold(r) as { child: child };
            loop {
                owns child: leaf();
                invariant child.model == LeafModel::Unit;
                invariant n >= 0;

                initialize by simp;
                preserve by {
                    have 0 <= n - 1 by {
                        apply(int32_positive_predecessor_is_nonnegative(n)) using {
                            n > 0;
                        }
                        assumption();
                    }
                    have n - 1 >= 0 by {
                        apply(int32_le_implies_reversed_ge(0, n - 1)) using {
                            0 <= n - 1;
                        }
                        assumption();
                    }
                    step();
                    close_invariants();
                }
            }
            let out = fold(root(), {
                model: RootModel::Has(LeafModel::Unit)
            }, { child: child });
            step();
            simp();
        },
    }
}
```

```termination
pending: unranked loop
```

```expect
pass
```
