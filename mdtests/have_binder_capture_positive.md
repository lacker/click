# Valid nested universal introductions remain provable

```c filename=have_binder_capture_positive.c
int32 good(int32 x) {
    return x;
}
```

```click
verifying "have_binder_capture_positive.c";

int32 good(int32 x) {
    requires x == 5;
    ensures result == 5;
} by {
    have forall (u: int32) {
        u == 5 implies forall (z: int32) { z == 5 implies z == 5 }
    } by {
        intro();
        intro();
        have forall (w: int32) { w == 5 implies w == 5 } by {
            intro();
            intro();
            assumption();
        }
        intro();
        intro();
        assumption();
    }
    step();
    simp();
}
```

```expect
pass
```
