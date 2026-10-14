# a mutually recursive model measure call must pass a smaller list

`walk_odd` passes its own `p` back to `walk_even` instead of `p->next`. The
proof folds the list it unfolded back into `x`, so the call can be applied, and
then owes the callee's measure below `walk_odd`'s entry reading. The list is
the same one, its measure is equal rather than smaller, and the descent is
refused.

```c filename=c_decreases_model_measure_mutual_recursion_must_descend_even.c
struct node { struct node *next; };

int32 walk_even(struct node* p) {
    int32 result;
    if (p != 0) {
        result = walk_odd(p->next);
        return result;
    }
    return 0;
}
```

```c filename=c_decreases_model_measure_mutual_recursion_must_descend_odd.c
struct node { struct node *next; };

int32 walk_odd(struct node* p) {
    int32 result;
    if (p != 0) {
        result = walk_even(p);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_model_measure_mutual_recursion_must_descend_even.c";
verifying "c_decreases_model_measure_mutual_recursion_must_descend_odd.c";

spec enum Links { Nil, Cons(Links) }

function links_len(m: Links) -> Integer
    decreases m
{
    match m {
        Links::Nil => 0,
        Links::Cons(rest) => links_len(rest) + 1,
    }
}

theorem links_len_is_nonnegative(m: Links) {
    ensures 0 <= links_len(m) by {
        induct(m) as ih {
            Links::Nil => {
                unfold(links_len(Links::Nil));
                normalize();
            }
            Links::Cons(rest) => {
                apply(ih(rest));
                unfold(links_len(Links::Cons(rest)));
                arithmetic() using { 0 <= links_len(rest); }
            }
        }
    }
}

resource list_at(p: struct node*) {
    field model: Links;
    match model {
        Links::Nil => { fact p == 0; },
        Links::Cons(rest_model) => {
            owns p->next;
            owns rest: list_at(p->next);
            fact p != 0;
            fact rest.model == rest_model;
        },
    }
}

int32 walk_even(struct node* p) {
    owns x: list_at(p);
    decreases links_len(x.model);
    ensures result == 0;
    ensures x.model == old(x.model);
} by {
    step();
    match x.model {
        Links::Nil => {
            unfold(x);
            step();
            let x = fold(list_at(p), { model: Links::Nil });
            step();
            step();
            simp();
        },
        Links::Cons(rest_model) => {
            let { rest: r } = unfold(x);
            apply(links_len_is_nonnegative(rest_model));
            have 0 <= links_len(r.model) by {
                rewrite(r.model == rest_model);
                assumption();
            }
            have links_len(old(x.model)) == links_len(rest_model) + 1 by {
                rewrite(old(x.model) == Links::Cons(rest_model));
                unfold(links_len(Links::Cons(rest_model)));
                normalize();
            }
            have links_len(r.model) < links_len(old(x.model)) by {
                rewrite(r.model == rest_model);
                arithmetic() using { links_len(old(x.model)) == links_len(rest_model) + 1; }
            }
            step();
            step();
            let x = fold(list_at(p), { model: Links::Cons(rest_model) }, { rest: r });
            step();
            simp();
        },
    }
}

int32 walk_odd(struct node* p) {
    owns x: list_at(p);
    decreases links_len(x.model);
    ensures result == 0;
    ensures x.model == old(x.model);
} by {
    step();
    match x.model {
        Links::Nil => {
            unfold(x);
            step();
            let x = fold(list_at(p), { model: Links::Nil });
            step();
            step();
            simp();
        },
        Links::Cons(rest_model) => {
            let { rest: r } = unfold(x);
            have p != 0;
            let x = fold(list_at(p), { model: Links::Cons(rest_model) }, { rest: r });
            apply(links_len_is_nonnegative(Links::Cons(rest_model)));
            step();
            step();
            step();
            simp();
        },
    }
}
```

```expect
fail: `links_len(x.model)` decreases at the recursive call
```
