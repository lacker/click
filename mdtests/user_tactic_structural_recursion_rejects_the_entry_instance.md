# a tactic cannot recurse on the instance it was given

This `convert` hands its own `x` straight back to itself, which would never
terminate. The measure at the application is the measure at entry, so its
descent cannot be established, and the application is refused for the first
structural descent obligation.

```c filename=user_tactic_structural_recursion_rejects_the_entry_instance.c
struct node { struct node *next; };

void user(struct node *p) {
}
```

```click
verifying "user_tactic_structural_recursion_rejects_the_entry_instance.c";

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
    decreases x;
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
fail: convert recursion measure `decreases x` does not descend
```
