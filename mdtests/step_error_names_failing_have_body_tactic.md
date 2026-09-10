# step failure names the tactic the user wrote

A failing proof step is reported by where it was written: the claim's source
tactic occurrence, then its position inside each enclosing `have` body. The
proof-tree depth is never reported as if it were a step number, so two
failures at the same depth in different `have` blocks report different
locations.

Here the second first-level `have` is source tactic 1, and its failing
`normalize()` is the second tactic of that body.

```c filename=two_haves.c
int32 two_haves(int32 x) {
    return x;
}
```

```click
verifying "two_haves.c";

int32 two_haves(int32 x) {
    requires x > 0;
    ensures result == x by {
        have x > 0 by {
            assumption();
        }
        have x >= 0 by {
            have x > 0 by {
                assumption();
            }
            normalize();
        }
        step();
        simp();
    }
}
```

```expect
fail: `two_haves.ensures_0` proof step source tactic 1 > have body tactic 2: `normalize` goal did not normalize to true
```
