# Explicit loop-invariant closure proof

The `by` keyword introduces a proof of the exact back-edge obligations.
Expansion retains its child scopes, rather than restating the goals as haves.
The completed body supplies the closure evidence; the legacy invariant prover
does not independently prove these obligations again. Read-safety obligations
are part of the body goal, not assumptions supplied to it.

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
        decreases 3 - i;
        invariant i >= 0;
        invariant i <= 3;
        initialize by simp;
        preserve by {
            mark iteration;
            step();
            close_invariants by {
                both { simp(); }
                and {
                    both { simp(); }
                    and { both { arithmetic() using { at(iteration, i) < 3; at(iteration, i) >= 0; } }
                        and { arithmetic() using { at(iteration, i) < 3; at(iteration, i) >= 0; } } }
                }
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
