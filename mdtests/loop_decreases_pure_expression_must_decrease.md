# a pure loop measure still has to decrease

The measure is the same pure application the positive case uses, and its
nonnegativity closes for the same reason. What the body never does is write
the cell the measure reads: it counts `box[1]` down while `head(box)` reads
`box[0]`. The back edge therefore compares the measure against itself, and the
ranking member stays open. A pure component buys no leniency: the obligation
is the one a C measure produces.

```c filename=loop_decreases_pure_expression_must_decrease.c
int32 drain(int32 box[4]) {
    while (box[1] > 0) {
        box[1] = box[1] - 1;
    }
    return box[1];
}
```

```click
verifying "loop_decreases_pure_expression_must_decrease.c";

function head(a: int32[]) -> int32 {
    a[0]
}

int32 drain(int32 box[4]) {
    owns box[0..4];
    requires box[0] >= 0;
    requires box[1] >= 0;
    ensures result == 0;
} by {
    loop {
        decreases head(box);
        invariant 0 <= box[0];
        invariant 0 <= box[1];
        invariant head(box) == box[0];
        initialize by { unfold(head(box)); simp(); }
        preserve by {
            have 0 <= box[1] - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(box[1])) using {
                    box[1] > 0;
                }
            }
            step();
            close_invariants by { unfold(head(box)); simp(); };
        }
    }
    step();
    simp();
}
```

```expect
fail: `head(box)` decreases at the back edge
```
