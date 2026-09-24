# A decided C branch in a loop body expands to a checked execution split

The loop body's C `if` tests `a[i] == 0`, which the precondition refutes, so
the kernel decides the branch: only the `else` arm is feasible. The proof
spells that with `branch { then { contradiction(...) } else { step(); } }`.
The checked certificate records a decided branch as a logical `if` over the
C condition whose infeasible arm is empty, and whole-claim expansion prints
it that way.

A preservation proof must read that expanded `if` as the checked C split it
spells, as a function body does, not as a proof-level case split. Read as a
case split, the empty `then` arm kept the refuted path alive, the
continuation's `step()` ran the C `then` arm on it, and the expanded
certificates for the feasible path no longer matched: `click expand --claim`
emitted a rewrite that did not verify. `src/surface/tests/expansion_tests.rs`
expands this claim and reverifies it.

```c filename=loop_preserve_decided_branch_expands.c
int32 count_zero_run(int32* a, int32 n) {
    int32 i;
    int32 c;
    i = 0;
    c = 0;
    while (i < n) {
        if (a[i] == 0) {
            c = c + 1;
        } else {
            c = 0;
        }
        i = i + 1;
    }
    return c;
}
```

```click
verifying "loop_preserve_decided_branch_expands.c";

int32 count_zero_run(int32* a, int32 n) {
    views a[0..n];
    requires 0 <= n;
    requires forall (k: int32) { 0 <= k and k < n implies a[k] == 1 };
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant c == 0;
        initialize by simp;
        preserve by {
            mark iteration;
            have a[i] == 1 by {
                instantiate(forall (k: int32) { 0 <= k and k < n implies a[k] == 1 }, i) using {
                    0 <= i;
                    i < n;
                }
                assumption();
            }
            have i + 1 <= n by {
                apply(int32_increment_upper_bound(i, n)) using { i < n; }
            }
            branch {
                then { contradiction(a[i] == 0); }
                else {
                    step();
                }
            }
            step();
            have 0 <= i and i <= n by { simp(); }
            have c == 0 by { simp(); }
            have 0 <= 0 - at(iteration, i) + n - 1 by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    at(iteration, i) < n;
                    0 <= n;
                }
            }
            have 0 - at(iteration, i) + n - 1 < 0 - at(iteration, i) + n by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    at(iteration, i) < n;
                    0 <= n;
                }
            }
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
