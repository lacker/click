# a structural binder measure refuses a call that passes the same list

`walk_odd` folds the list it unfolded back into `x` and passes it, with `p`,
to `walk_even`. The instance passed is the one `walk_odd` held at its entry,
not a contained child of it, so the descent is refused.

```c filename=c_decreases_binder_measure_mutual_recursion_must_descend_even.c
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

```c filename=c_decreases_binder_measure_mutual_recursion_must_descend_odd.c
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
verifying "c_decreases_binder_measure_mutual_recursion_must_descend_even.c";
verifying "c_decreases_binder_measure_mutual_recursion_must_descend_odd.c";

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
            have p != 0;
            let x = fold(list_at(p), { model: Links::Cons(rest_model) }, { rest: r });
            step();
            step();
            step();
            simp();
        },
    }
}
```

```expect
fail: `decreases x` does not descend
```
