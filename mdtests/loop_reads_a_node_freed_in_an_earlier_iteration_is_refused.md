# a loop cannot read a node it freed in an earlier iteration

`prev` keeps the node the previous iteration freed, and the body reads
`prev->next`. The loop head does not record that allocation's tombstone, but
reading through `prev` needs authority over the cell, which no resource the
loop holds grants, so the read is refused.

```c filename=loop_reads_a_node_freed_in_an_earlier_iteration_is_refused.c
struct node {
    struct node *next;
};

void release(struct node *p) {
    struct node *prev = 0;
    while (p != 0) {
        struct node *next = p->next;
        if (prev != 0) {
            next = prev->next;
        }
        free(p);
        prev = p;
        p = next;
    }
}
```

```click
verifying "loop_reads_a_node_freed_in_an_earlier_iteration_is_refused.c";

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
            owns allocation(p, sizeof(struct node));
            owns *p;
            owns rest: list_at(p->next);
            fact p != 0;
            fact rest.model == rest_model;
        },
    }
}

void release(struct node* p) {
    consumes x: list_at(p);
} by {
    step();
    step();
    loop {
        owns x: list_at(p);
        decreases links_len(x.model);

        initialize by close();
        maintain by {
            match x.model {
                Links::Nil => { contradiction(x.model == Links::Nil); },
                Links::Cons(rest_model) => {
                    apply(links_len_is_nonnegative(rest_model));
                    have links_len(x.model) == links_len(rest_model) + 1 by {
                        rewrite(x.model, Links::Cons(rest_model));
                        unfold(links_len(Links::Cons(rest_model)));
                        close();
                    }
                    have links_len(rest_model) < links_len(x.model) by {
                        close() using { links_len(x.model) == links_len(rest_model) + 1; };
                    }
                    let { rest: r } = unfold(x);
                    have 0 <= links_len(r.model) by {
                        rewrite(r.model, rest_model);
                        close();
                    }
                    step();
                    step();
                    branch {
                        true => {
                            step();
                        }
                        false => {}
                    }
                    step();
                    step();
                    step();
                },
            }
        }
    }
    unfold(x);
    step();
    close();
}
```

```expect
fail: access outside the subobject the pointer designates
```
