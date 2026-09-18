# preservation proof branches through one loop iteration

An explicit preservation proof can use the ordinary proof-level `if` and
branch-entry execution steps. Each proof branch must reach the loop back edge
and reestablish the complete invariant set, including the ranking obligations
the `decreases` clause adds. The `i < 0` arm cannot happen — the invariant
`i >= 0` rules it out — but the proof still walks it to the back edge, so its
decrease obligation is closed by `contradiction`, citing the arm guard whose
negation the invariant already states.

```c filename=loop_preserve_branch.c
int32 loop_preserve_branch(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        if (i < 0) {
            i = 0;
        } else {
            i = i + 1;
        }
    }
    return i;
}
```

```click
verifying "loop_preserve_branch.c";

int32 loop_preserve_branch(int32 n) {
    requires n >= 0 and n <= 2147483647;
    ensures result == n;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= n;
        decreases n - i;
        preserve by {
            if i < 0 {
                step();
                step();
                close_invariants by {
                    both { simp(); }
                    and {
                        both { simp(); }
                        and { contradiction(at(statement(3).entry, i) < 0); }
                    }
                }
            } else {
                have i + 1 >= 0 by {
                    apply(int32_increment_greater_equal_lower_bound(i, 0, n)) using { i >= 0; i < n; }
                }
                step();
                step();
                close_invariants by { simp(); }
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
