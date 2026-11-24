# a recursive tactic needs a `decreases` measure

`convert` applies itself with no `decreases`. A recursion nothing ranks could
justify its own contract, so termination refuses it, and a tactic, unlike a C
function, may not be declared `diverges` instead.

```c filename=user_tactic_recursion_needs_a_measure.c
struct node { struct node *next; };

void user(struct node *p) {
}
```

```click
verifying "user_tactic_recursion_needs_a_measure.c";

spec enum Links { Nil, Cons(Links) }

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
fail: rank tactic `convert` with an expression `decreases`
```
