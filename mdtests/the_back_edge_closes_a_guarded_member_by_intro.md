# the smart closer introduces a guarded member's guard

`count_run` counts how far `i` has advanced past `2`. The third invariant says
so with `2 + run == i`, and `2 + run` is an `int32` addition, so the back-edge
bundle states that member under its definedness guard:
`defined(2 + run) implies ...`. The ranking members follow it, so on the
`else` arm the bundle is a conjunction whose first conjunct is that
implication.

Every leaf is already a fact: the body states the disjunction with `close()`
and proves the two ranking inequalities over exact Integers. The member
compares `to_integer(2 + run)` with `to_integer(i)`, so the `else` arm first
derives `defined(2 + run)` from the incremented `run`'s Integer bounds. It also
records the corresponding equality with addition in Integer arithmetic for
expansion replay. The closing proof is
an `all` block with `intro(); close();` in its guarded arm, and the back edge's closer
must find it by splitting the bundle and closing each conjunct with the
direct logical steps, before the premise-selecting and rewriting strategies
run over the whole bundle. Before that, this arm fell through to the indexed
goal-equality rewrite and the structural derivation, and on the arena
example the same shape crossed the smart tactic's time limit.

```c filename=the_back_edge_closes_a_guarded_member_by_intro.c
int32 count_run(int32 n) {
    int32 i = 0;
    int32 run = 0;

    while (i < n) {
        if (i < 2) {
            run = 0;
        } else {
            run = run + 1;
        }
        i = i + 1;
    }
    return run;
}
```

```click
import click::integer;
verifying "the_back_edge_closes_a_guarded_member_by_intro.c";

int32 count_run(int32 n) {
    requires 0 <= n;
    ensures 0 <= result;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases to_integer(n) - to_integer(i);
        invariant 0 <= i and i <= n;
        invariant 0 <= run and run <= i;
        invariant (i <= 2 and run == 0) or (2 <= i and to_integer(2 + run) == to_integer(i));

        initialize by close();
        maintain by {
            mark iteration;
            if i < 2 {
                branch { true => { step(); } false => { contradiction(not (i < 2)); } }
                step();
                have 0 <= i and i <= n;
                have 0 <= run and run <= i;
                have i <= 2 and run == 0;
                have (i <= 2 and run == 0) or (2 <= i and to_integer(2 + run) == to_integer(i)) by close();
                have 0 <= to_integer(n) - to_integer(i) by {
                    close() using { i <= n; };
                }
                have to_integer(n) - to_integer(i) < to_integer(n) - to_integer(at(iteration, i)) by {
                    have to_integer(i) == to_integer(at(iteration, i)) + 1;
                    rewrite(to_integer(i), to_integer(at(iteration, i)) + 1);
                    close();
                }
            } else {
                have 2 <= i by { close() using { not (i < 2); }; }
                have to_integer(2 + run) == to_integer(i) by {
                    cases {
                        (i <= 2 and run == 0) => {
                            have i == 2;
                            rewrite(run, 0);
                            rewrite(i, 2);
                            close() using { i <= 2; };
                        }
                        (2 <= i and to_integer(2 + run) == to_integer(i)) => {
                            have to_integer(2 + run) == to_integer(i);
                            close();
                        }
                    }
                }
                have run < n by {
                    close() using {
                        run <= i;
                        i < n;
                    };
                }
                branch { true => { contradiction(i < 2); } false => { step(); } }
                step();
                have 0 <= i and i <= n;
                have 0 <= run and run <= i;
                have to_integer(run) == to_integer(at(iteration, run)) + 1;
                have to_integer(i) == to_integer(at(iteration, i)) + 1;
                have to_integer(2 + at(iteration, run)) == to_integer(at(iteration, i));
                have to_integer(2 + at(iteration, run)) == 2 + to_integer(at(iteration, run));
                have to_integer(2) + to_integer(run) <= 2147483647;
                have to_integer(2) + to_integer(run) >= -2147483648;
                have defined(2 + run);
                have 2 <= i and to_integer(2 + run) == to_integer(i);
                have (i <= 2 and run == 0) or (2 <= i and to_integer(2 + run) == to_integer(i)) by close();
                have to_integer(2 + run) == 2 + to_integer(run) by {
                    normalize() using {
                        to_integer(2) + to_integer(run) >= -2147483648;
                        to_integer(2) + to_integer(run) <= 2147483647;
                    };
                }
                have (i <= 2 and run == 0) or (2 <= i and 2 + to_integer(run) == to_integer(i)) by {
                    rewrite(2 + to_integer(run), to_integer(2 + run));
                    close();
                }
                have 0 <= to_integer(n) - to_integer(i) by {
                    close() using { i <= n; };
                }
                have to_integer(n) - to_integer(i) < to_integer(n) - to_integer(at(iteration, i)) by {
                    have to_integer(i) == to_integer(at(iteration, i)) + 1;
                    rewrite(to_integer(i), to_integer(at(iteration, i)) + 1);
                    close();
                }
            }
        }
    }
    step();
    close();
}
```

```expect
pass
```
