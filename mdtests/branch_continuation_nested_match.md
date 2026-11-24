# A proof `match` in a `branch` continuation keeps the branch's attribution

The outer `match` arm runs a `branch` whose `true` arm returns and whose
`false` arm continues into the rest of the arm: a nested proof `match` that
runs to function exit inside the `false` arm, splitting at the C's second `if`
with a proof `if` whose cases each step to exit with
`step_until(function.exit)`. A proof `match` attributes its
diagnostics to its own tactic while it runs. It used to leave the shared arm
proof attributed to itself afterwards, so the branch's certificate
checkpoint no longer matched the joined proof's context and a valid proof
failed with an internal "certificate checkpoint belongs to a different proof
context" error. The match now restores its owner's attribution, and the
branch restores its own after the join, as the neighbouring `if` and
call-outcome joins do. The expansion regression in
`src/surface/tests/expansion_tests.rs` expands this claim and re-verifies
the rewrite.

```c filename=t5.c
int32 f(int32* p, int32 x) {
    if (x <= 0) {
        return 0;
    }
    if (x < 5) {
        return 0;
    }
    return 1;
}
```

```click
verifying "t5.c";

spec enum T { A(int32) }

resource r(p: int32*) {
    field m: T;
    match m {
        T::A(v) => {
            owns p[0..1];
        },
    }
}

int32 f(int32* p, int32 x) {
    owns c: r(p);
    ensures result == 0 or result == 1;
} by {
    match c.m {
        T::A(v) => {
            branch {
                true => {
                    step();
                    close();
                }
                false => {}
            }
            match c.m {
                T::A(w) => {
                    if x < 5 {
                        step_until(function.exit);
                    } else {
                        step_until(function.exit);
                    }
                },
            }
        },
    }
}
```

```expect
pass
```
