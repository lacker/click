# a loop measure may be a pure expression

The measure is not a C expression at all: it is an application of a pure Click
function to the array the loop writes. The kernel evaluates that one declared
expression at the iteration-entry state and again at the back edge, exactly as
it evaluates an invariant about the same cells at those two states, and the
ranking members it builds are the same two obligations a C measure produces.

The application stays opaque, so the proof unfolds it on the back-edge side
and carries `head(box) == box[0]` as an invariant to name the iteration-entry
side. Nothing else changes: `decreases box[0]` would need the same `have`.

```c filename=loop_decreases_pure_expression.c
int32 drain(int32 box[4]) {
    while (box[0] > 0) {
        box[0] = box[0] - 1;
    }
    return box[0];
}
```

```click
verifying "loop_decreases_pure_expression.c";

function head(a: int32[]) -> int32 {
    a[0]
}

int32 drain(int32 box[4]) {
    owns box[0..4];
    requires box[0] >= 0;
    ensures result == 0;
} by {
    loop {
        decreases head(box);
        invariant 0 <= box[0];
        invariant head(box) == box[0];
        initialize by { unfold(head(box)); simp(); }
        preserve by {
            have 0 <= box[0] - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(box[0])) using {
                    box[0] > 0;
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
pass
```
