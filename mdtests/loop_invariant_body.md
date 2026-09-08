# Explicit loop-invariant closure proof

The `by` keyword introduces a proof of the exact back-edge obligations.
Expansion retains its child scopes, rather than restating the goals as haves.

```c filename=count.c
int32 count() {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "count.c";

int32 count() { ensures result == 3; } by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= 3;
        initialize by simp;
        preserve by {
            step();
            close_invariants by {
                both { simp(); } and { simp(); }
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
