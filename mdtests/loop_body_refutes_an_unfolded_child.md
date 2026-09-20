# The path refutes an unfolded child's arm where it stands

D7 in reverse says that a premise refuting an arm's own fact publishes the
model fact that refutation forces. Package A13 wired that at contract lowering,
at a loop head, at a back edge and at the `unfold` that introduces a child.
None of those is where a loop body learns what its child is.

`countdown_two` unfolds `c` to reach `rest`, then decrements. Whether the body
takes a second step down is settled by the C local `n` *after* that decrement,
which is a fact of the proof-level `if`'s arm and of nothing earlier: at the
`unfold` the cursor had not moved yet, and at the loop head the guard spoke
about the frame above. So the child's arms are decided at the arm of the `if`,
against the facts standing there — `n != 0` refutes `chain`'s `Nil` arm, whose
own fact is `k == 0`, and `n == 0` refutes its `Link` arm, whose own fact is
`k != 0`, which leaves `Nil` as the only value the model can have and gives the
bare `unfold(r)` its constructor.

Both directions are published where they are decided: the case split a proof
`match` issues carries them into every arm, and an `unfold` states the model
fact that chose the arm it opened, so the back edge still sees that the
instance the binder holds is the child this path descended into.

This is the shape of every rbtree fixup body that climbs two frames: the uncle
case reads `rb_parent(node)` and only then knows whether the frame above the
one it just left is `Context::Top`.

Before package A26 the `contradiction` was refused with `constructor-arm
`contradiction` requires an exact fact and its negation in that arm`, and the
body had to nest a proof `match` over the child and carry both cases through
the rest of the iteration
([`loop_decreases_strict_descendant.md`](loop_decreases_strict_descendant.md)
is that spelling).

```c filename=countdown_two.c
void countdown_two(int32 n) {
    while (n > 0) {
        n = n - 1;
        if (n != 0) {
            n = n - 1;
        }
    }
}
```

```click
verifying "countdown_two.c";

spec enum Chain { Nil, Link(Chain) }

resource chain(k: int32) {
    field model: Chain;
    match model {
        Chain::Nil => { fact k == 0; },
        Chain::Link(rest_model) => {
            owns rest: chain(k - 1);
            fact k != 0;
            fact k > 0;
            fact k - 1 >= 0;
            fact rest.model == rest_model;
        },
    }
}

void countdown_two(int32 n) {
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
                    let { rest: r } = unfold(c);
                    step();
                    if n != 0 {
                        match r.model {
                            Chain::Nil => { contradiction(r.model == Chain::Nil); },
                            Chain::Link(rest2_model) => {
                                let { rest: r2 } = unfold(r);
                                step();
                                step();
                                close_invariants();
                            },
                        }
                    } else {
                        unfold(r);
                        step();
                        step();
                        let c = fold(chain(n), { model: Chain::Nil });
                        close_invariants();
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
