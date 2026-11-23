# `intro` must not capture an ambient variable

```c filename=have_binder_capture.c
int32 bad(int32 x) {
    while (x < 1) {
        x = x + 1;
    }
    return x;
}
```

```click
verifying "have_binder_capture.c";

int32 bad(int32 x) {
    requires x == 0;
    ensures result == 5;
} by {
    loop {
        invariant x == 5;
        initialize by {
            have forall (u: int32) {
                u == 5 implies forall (z: int32) { z == 5 }
            } by {
                intro();
                intro();
                have forall (w: int32) { w == 5 } by {
                    intro();
                    known();
                }
                known();
            }
            have x == 5 by {
                have 5 == 5;
                instantiate(
                    forall (u: int32) {
                        u == 5 implies forall (z: int32) { z == 5 }
                    },
                    5
                );
                instantiate(
                    forall (z: int32) { z == 5 },
                    x
                );
                known();
            }
            known();
        }
        maintain by {
            have forall (u: int32) {
                u == 5 implies forall (z: int32) { z == 5 }
            } by {
                intro();
                intro();
                have forall (w: int32) { w == 5 } by {
                    intro();
                    known();
                }
                known();
            }
            have x == 5 by {
                have 5 == 5;
                instantiate(
                    forall (u: int32) {
                        u == 5 implies forall (z: int32) { z == 5 }
                    },
                    5
                );
                instantiate(
                    forall (z: int32) { z == 5 },
                    x
                );
                known();
            }
            known();
        }
    }
    step();
    solve();
}
```

```expect
fail: have body tactic 2: `known()` could not close the current goal
```
