# a loop that frees a node and then reads it is refused

The body frees `p` and then reads `p->next`. The free consumed the node's
storage, so the read is an invalid access inside the iteration, whatever the
loop join allows.

```c filename=loop_frees_a_node_then_reads_it_is_refused.c
struct node {
    struct node *next;
};

void release(struct node *p) {
    while (p != 0) {
        free(p);
        p = p->next;
    }
}
```

```click
verifying "loop_frees_a_node_then_reads_it_is_refused.c";

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
fail: invalid memory access
```
