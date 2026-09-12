# A `branch` decides a body `if` inside `preserve`

A ranked loop's `preserve` runs one certified iteration. When the body contains
an `if`, `branch` is the spelling that consumes it: each arm runs the source the
guard selects and the two rejoin at the statement after the `if`, so the back
edge sees one path and the measure is compared once. The proof-level `if` is the
other spelling, and it is the one to use when the arms must stay apart — an arm
that `break`s, or one whose resource state differs from its sibling's
([`loop_body_break_in_branch_arm_rejected.md`](loop_body_break_in_branch_arm_rejected.md)).

`loop_branch_body` is the plain case: both arms are feasible and the join is
described by the `branch`'s own `ensuring` interface.

`chain_countdown` puts the `branch` inside a proof `match` arm, where the loop
is ranked by the instance the binder holds rather than by a counter.

`chain_countdown_decided` is the shape package A24 could not write. The body's
`if` guard is already settled by the arm of `match r.model` the proof is in, so
one arm of the C `if` is infeasible and the `branch` is *decided*: it certifies
as a proof `if` with one empty arm. That certificate is the single path this
leaf took, not a case the validation path split at, so the preservation leaf's
case path charges it nothing. Before A26 the leaf was refused with `surface
certificate branch condition does not match its validation path`, and the body's
`if` had to be walked with bare `step()`s instead
([`loop_decreases_strict_descendant.md`](loop_decreases_strict_descendant.md)
is that spelling of the same C).

```c filename=loop_branch_body.c
int32 loop_branch_body(int32 n) {
    int32 i;
    int32 t;

    i = 0;
    t = 0;
    while (i < n) {
        if (i < 3) {
            t = 1;
        } else {
            t = 2;
        }
        i = i + 1;
    }
    return t;
}
```

```c filename=chain_branch_body.c
void chain_countdown(int32 n) {
    while (n > 0) {
        if (n > 1000) {
            n = n - 1;
        } else {
            n = n - 1;
        }
    }
}
```

```c filename=chain_decided_branch.c
void chain_countdown_decided(int32 n) {
    while (n > 0) {
        n = n - 1;
        if (n > 0) {
            n = n - 1;
        } else {
            n = 0;
        }
    }
}
```

```click
verifying "loop_branch_body.c";
verifying "chain_branch_body.c";
verifying "chain_decided_branch.c";

spec enum Chain { Nil, Link(Chain) }

resource chain(k: int32) {
    field model: Chain;
    match model {
        Chain::Nil => { fact k == 0; },
        Chain::Link(rest_model) => {
            owns rest: chain(k - 1);
            fact k > 0;
            fact k - 1 >= 0;
            fact rest.model == rest_model;
        },
    }
}

int32 loop_branch_body(int32 n) {
    requires n >= 0;
    requires n <= 1000;
    ensures result >= 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        invariant t >= 0;
        invariant t <= 100;

        initialize by simp;
        preserve by {
            branch {
                ensuring {
                    fact t >= 0;
                    fact t <= 100;
                }
                then { step(); }
                else { step(); }
            }
            step();
            close_invariants();
        }
    }
    step();
    simp();
}

void chain_countdown(int32 n) {
    requires n >= 0;
    consumes c: chain(n);
    ensures 1 == 1;
} by {
    loop {
        owns c: chain(n);
        decreases c;
        invariant n >= 0;

        initialize by simp;
        preserve by {
            match c.model {
                Chain::Nil => { contradiction(c.model == Chain::Nil); },
                Chain::Link(rest_model) => {
                    unfold(c) as { rest: r };
                    branch {
                        then { step(); }
                        else { step(); }
                    }
                    close_invariants();
                },
            }
        }
    }
    have n == 0 by { simp(); }
    unfold(c);
    step();
    simp();
}

void chain_countdown_decided(int32 n) {
    requires n >= 0;
    consumes c: chain(n);
    ensures 1 == 1;
} by {
    loop {
        owns c: chain(n);
        decreases c;
        invariant n >= 0;

        initialize by simp;
        preserve by {
            match c.model {
                Chain::Nil => { contradiction(c.model == Chain::Nil); },
                Chain::Link(rest_model) => {
                    unfold(c) as { rest: r };
                    match r.model {
                        Chain::Nil => {
                            unfold(r);
                            step();
                            branch {
                                then { step(); }
                                else { step(); }
                            }
                            let c = fold(chain(n), { model: Chain::Nil });
                            close_invariants();
                        },
                        Chain::Link(rest2_model) => {
                            unfold(r) as { rest: r2 };
                            step();
                            branch {
                                then { step(); }
                                else { step(); }
                            }
                            close_invariants();
                        },
                    }
                },
            }
        }
    }
    have n == 0 by { simp(); }
    unfold(c);
    step();
    simp();
}
```

```expect
pass
```
