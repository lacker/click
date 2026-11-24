# a tactic cannot recurse on the instance it was given

This `convert` hands its own `x` straight back to itself, which would never
terminate. The measure at the application is the measure at entry, so its
descent cannot be established, and the application is refused for the first
ranking fact it lacks.

```c filename=user_tactic_recursion_on_the_same_instance_is_refused.c
struct node { struct node *next; };

void user(struct node *p) {
}
```

```click
verifying "user_tactic_recursion_on_the_same_instance_is_refused.c";

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
            let { y: y } = convert(p, { x: x });
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
fail: (convert recursion measure:
```
