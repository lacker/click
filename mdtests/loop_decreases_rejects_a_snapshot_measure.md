# a loop measure may not name a fixed state

A measure is one expression the kernel reads at the iteration's entry state
and again at the back-edge state; the ranking obligation is that the second
value is smaller. A component that names a state of its own reads the same
state twice, so its two values are equal by construction and the back edge can
never close. `old(...)` used to lower and leave the bundle permanently open,
with nothing saying why. It is refused at the declaration instead.

```c filename=loop_decreases_rejects_a_snapshot_measure.c
int32 drain(int32 box[4]) {
    while (box[0] > 0) {
        box[0] = box[0] - 1;
    }
    return box[0];
}
```

```click
verifying "loop_decreases_rejects_a_snapshot_measure.c";

function head(a: int32[]) -> int32 {
    a[0]
}

int32 drain(int32 box[4]) {
    owns box[0..4];
    requires box[0] >= 0;
    ensures result == 0;
} by {
    loop {
        decreases old(head(box));
        invariant 0 <= box[0];
        initialize by simp;
        preserve by {
            step();
            simp();
        }
    }
    step();
    simp();
}
```

```expect
fail: names the fixed state `old(...)`
```
