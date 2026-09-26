# A finished arm closes its back edge before an unfinished sibling is reported

Neither constructor is excluded here, so the preservation region really splits:
each arm runs its own iteration, refolds its own instance, and closes the
invariants separately. The arms never rejoin — a preservation path does not
join across the back edge — so the loop rule is certified from two paths and
the preservation certificate is reassembled as the `match` that produced them.

The `Neg` arm of this `preserve` has been written only as far as its
`unfold`, while the `Pos` arm after it reaches its back edge with a closer
that proves nothing. Both are wrong, but only one is a mistake: a script still being
written is reported by the frontier it reached, and a finished path that does
not close the invariants is a failed proof. The finished arm's back edge is
checked first, so its failure is what the author sees, and the unfinished
sibling is reported once that is fixed. Before, the frontier report for the
unfinished arm was emitted the moment the region met it, so the arm after it
never ran and a wrong `close_invariants` there stayed silent until every arm
was finished.

```c filename=preserve_finished_arm_checked_before_frontier.c
struct cell { int32 value; };

void spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}
```

```click
verifying "preserve_finished_arm_checked_before_frontier.c";

spec enum Sign { Neg(int32), Pos(int32) }

resource cell(p: struct cell*) {
    field model: Sign;
    match model {
        Sign::Neg(value) => {
            owns p->value;
            fact p->value == value;
            fact value < 0;
        },
        Sign::Pos(value) => {
            owns p->value;
            fact p->value == value;
            fact value >= 0;
        },
    }
}

void spin(struct cell* node, int32 n) {
    requires n >= 0;
    requires node != 0;
    owns c: cell(node);
    ensures c.model == old(c.model);
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: cell(node);
        invariant i >= 0;
        invariant i <= n;
        invariant c.model == old(c.model);

        initialize by simp;
        preserve by {
            match c.model {
                Sign::Neg(value) => {
                    unfold(c);
                },
                Sign::Pos(value) => {
                    have Sign::Pos(value) == old(c.model) by {
                        simp() using { c.model == Sign::Pos(value); c.model == old(c.model); }
                    }
                    unfold(c);
                    step();
                    let c = fold(cell(node), { model: Sign::Pos(value) });
                    close_invariants by {
                        normalize();
                    }
                },
            }
        }
    }
    step();
    simp();
}
```

```expect
fail: goal did not normalize to true
```
