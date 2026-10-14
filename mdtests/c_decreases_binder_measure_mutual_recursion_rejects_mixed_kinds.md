# a component ranked by structural binders does not mix in an expression measure

`walk_even` is ranked by its binder and `walk_odd` by `links_len(x.model)`.
`walk_even`'s call to `walk_odd` has no structural measure to compare, so it
is refused by name.

```c filename=c_decreases_binder_measure_mutual_recursion_rejects_mixed_kinds_even.c
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

```c filename=c_decreases_binder_measure_mutual_recursion_rejects_mixed_kinds_odd.c
struct node { struct node *next; };

int32 walk_odd(struct node* p) {
    int32 result;
    if (p != 0) {
        result = walk_even(p->next);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_binder_measure_mutual_recursion_rejects_mixed_kinds_even.c";
verifying "c_decreases_binder_measure_mutual_recursion_rejects_mixed_kinds_odd.c";

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
    decreases x;
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
```

```expect
fail: `walk_odd` is in `walk_even`'s recursive component but declares no structural `decreases` binder
```
