# a structural binder measure ranks mutual recursion

`walk_even` and `walk_odd` alternate down a modeled list, each ranked by
`decreases x`, its own resource binder. In a recursive component of two or
more, such a measure is ranked at each call rather than by reading the body:
the instance a call passes for the callee's measured binder must hold a model
strictly contained in the model the caller's binder held at its entry, through
the arms this path's facts decide. That is the decision a loop's `decreases`
binder makes at its back edge. Here the arm unfolded `x`, so the child `r` it
passes carries the `Cons` arm's submodel, and no size function or descent
`have` is needed.

```c filename=c_decreases_binder_measure_mutual_recursion_even.c
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

```c filename=c_decreases_binder_measure_mutual_recursion_odd.c
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
verifying "c_decreases_binder_measure_mutual_recursion_even.c";
verifying "c_decreases_binder_measure_mutual_recursion_odd.c";

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
```

```expect
pass
```
