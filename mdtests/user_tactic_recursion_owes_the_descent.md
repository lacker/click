# a recursive tactic application owes its measure's descent

The positive example without the `have` that proves the measure decreases.
The recursive application is refused, naming the descent it owes.

```c filename=user_tactic_recursion_owes_the_descent.c
struct node { struct node *next; };

void user(struct node *p) {
}
```

```click
verifying "user_tactic_recursion_owes_the_descent.c";

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
        let ih = induct(m);
        match m {
            Links::Nil => {
                unfold(links_len(Links::Nil));
                normalize();
            }
            Links::Cons(rest) => {
                apply(ih(rest));
                unfold(links_len(Links::Cons(rest)));
                close() using { 0 <= links_len(rest); };
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

resource list2_at(p: struct node*) {
    field model: Links;
    match model {
        Links::Nil => { fact p == 0; },
        Links::Cons(rest_model) => {
            owns p->next;
            owns rest: list2_at(p->next);
            fact p != 0;
            fact rest.model == rest_model;
        },
    }
}

tactic convert(p: struct node*) {
    consumes x: list_at(p);
    decreases links_len(x.model);
    produces y: list2_at(p);
    ensures y.model == old(x.model);
} by {
    match x.model {
        Links::Nil => {
            unfold(x);
            let y = fold(list2_at(p), { model: Links::Nil });
            have y.model == old(x.model);
        },
        Links::Cons(rest_model) => {
            let { rest: r } = unfold(x);
            apply(links_len_is_nonnegative(rest_model));
            have 0 <= links_len(r.model) by {
                rewrite(r.model, rest_model);
                close();
            }
            have links_len(old(x.model)) == links_len(rest_model) + 1 by {
                rewrite(old(x.model), Links::Cons(rest_model));
                unfold(links_len(Links::Cons(rest_model)));
                close();
            }
            let { y: r2 } = convert(p->next, { x: r });
            have r2.model == rest_model;
            let y = fold(list2_at(p), { model: Links::Cons(rest_model), rest: r2 });
            have y.model == old(x.model);
        },
    }
}

void user(struct node* p) {
    consumes a: list_at(p);
    produces b: list2_at(p);
} by {
    let { y: b } = convert(p, { x: a });
    step();
    step();
    close();
}
```

```expect
fail: `links_len(x.model)` decreases at the recursive call
```
