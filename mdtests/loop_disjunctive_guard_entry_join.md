# A disjunctive loop guard enters by one path per disjunct

`while (a > 0 || b > 0)` is the mirror image of a short-circuit conjunction: it
has one way *out* and two ways *in* — `a` is positive, or `a` is not and `b`
is. The loop rule runs the body once per entry path, and each path carries
only its own guard facts. One preserve body serves them all, so a proof that
needs the guard has nothing to split on: whatever it writes must read the same
way on every entry path, and two paths that close differently produce
different preservation certificates for the same written proof.

So the entry paths export their join, exactly as
[`loop_conjunctive_guard_exit_join.md`](loop_conjunctive_guard_exit_join.md)
joins the guard-false exits: every fact all the entry paths state, followed by
the disjunction of what each one states alone, `a > 0 or b > 0`. A conjunct
another entry path contradicts is dropped, which only weakens that disjunct
and so keeps the disjunction true. The disjuncts are in short-circuit
evaluation order — the path that decided the guard on `a` alone comes first —
so the disjunction reads the way the C guard does rather than the order the
kernel happened to enumerate the paths in.

`cases` over that disjunction is what makes one written proof serve both
paths: each arm assumes its own disjunct on *every* path, so both paths run
the same tactics and agree on the certificate. Here the loop's measure needs
it — `a + b` decreases to zero, and only the guard says it started above it.

```c filename=loop_disjunctive_guard_entry_join.c
int32 enters_either_way(int32 a, int32 b) {
    while (a > 0 || b > 0) {
        a = 0;
        b = 0;
    }
    return a + b;
}
```

```click
verifying "loop_disjunctive_guard_entry_join.c";

int32 enters_either_way(int32 a, int32 b) {
    requires a >= 0;
    requires a <= 1;
    requires b >= 0;
    requires b <= 1;
    ensures result == 0;
} by {
    loop {
        decreases a + b;
        invariant a >= 0;
        invariant a <= 1;
        invariant b >= 0;
        invariant b <= 1;
        preserve by {
            have 0 < a + b by {
                cases(a > 0 or b > 0) {
                    arithmetic() using { a > 0; b >= 0; a <= 1; b <= 1; }
                } {
                    arithmetic() using { b > 0; a >= 0; a <= 1; b <= 1; }
                }
            }
            step();
            step();
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
