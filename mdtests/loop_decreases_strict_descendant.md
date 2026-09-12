# a structural loop measure accepts a strict descendant

`decreases c;` ranks a loop by the instance its binder holds, and the rule was
that the back edge hands back a *direct contained child* of that instance. A
body that takes one step down hands back `rest`. A body that takes two hands
back `rest.rest`, which is nobody's direct child, and the measure refused it
with `does not descend: ... is not a direct contained child`.

Every rbtree fixup loop moves that way. `__rb_insert`'s uncle-red case
recolours the parent and the uncle black, sets `node = gparent`, and goes round
again, so the frame the next iteration starts at is two above the one this
iteration started at ([`rb_insert_color.md`](rb_insert_color.md)). Ranking such
a loop by a counter would be a different claim; the structure it walks is the
true measure.

The rule is now a strict contained descendant, reached through the arms this
path has already decided. That is not a search. Every step down needs a premise
naming that instance's constructor, and the only thing that produces one is the
body unfolding it: here the body unfolds `c` to reach `r`, then unfolds `r` to
reach `r2`, and the measure follows exactly those two links, in the resource
definition, with the submodel each child carries. An instance the body never
unfolded decides nothing and the walk stops there, so a back edge that stays
put is still refused by name
([`loop_decreases_rejects_same_instance.md`](loop_decreases_rejects_same_instance.md)),
and so is one that hands back an unrelated instance
([`loop_decreases_rejects_unrelated_node.md`](loop_decreases_rejects_unrelated_node.md)).
A model is a finite inductive term, so a strictly deeper submodel at every back
edge is well-founded for the same reason a direct child was.

`chain` owns no memory and the contract claims nothing but termination, so the
descent is the whole of what is under test. The `if` is what makes both lengths
of iteration reachable: the last iteration takes one step, every other takes
two, and one `decreases c` has to accept both. Which of the two the body takes
is settled before the statement runs, because the arm of `match r.model` the
proof is in already fixes whether `n` is zero after the first decrement.
`fact k - 1 >= 0;` is there for the same reason the arm's other facts are: the
second `unfold` evaluates its own child's argument, and a resource body states
what its members need.

```c filename=loop_decreases_strict_descendant.c
void countdown(int32 n) {
    while (n > 0) {
        n = n - 1;
        if (n > 0) {
            n = n - 1;
        }
    }
}
```

```click
verifying "loop_decreases_strict_descendant.c";

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

void countdown(int32 n) {
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
                            step();
                            step();
                            let c = fold(chain(n), { model: Chain::Nil });
                            close_invariants();
                        },
                        Chain::Link(rest2_model) => {
                            unfold(r) as { rest: r2 };
                            step();
                            step();
                            step();
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
