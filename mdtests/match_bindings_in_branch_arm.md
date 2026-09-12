# Match-arm bindings stay in scope inside a nested branch arm

A proof `match` on a resource's model binds the selected constructor's fields
for the rest of the arm, including the arms of a `branch` written inside it.
Those inner tactics are scheduled after execution reaches the function's
outcome, so the arm's binding scope has to travel with them: without it a
`rewrite` or `have` written one `branch` deep reports that the payload is not
a binding in this scope, and there is no place left to state the bridge
between a C pointer and the model's identity payload.

Here `Chain::Link` carries both kinds of payload, a `struct node*` identity and
a nested `Chain`. The postcondition names both, and the pair of `have` steps
that proves it is written once inside the second `branch` arm and once in the
arm's continuation, so the same bindings have to resolve in both places.

```c filename=chain_scope.c
struct node {
    struct node *next;
};

int chain_has_next(struct node *p) {
    if (p == 0) {
        return 0;
    }
    if (p->next == 0) {
        return 0;
    }
    return 1;
}
```

```click
verifying "chain_scope.c";

spec enum Chain {
    End,
    Link(struct node*, Chain),
}

resource chain_at(p: struct node*) {
    field model: Chain;
    match model {
        Chain::End => { fact p == 0; },
        Chain::Link(identity, rest_model) => {
            owns p->next;
            owns rest: chain_at(p->next);
            fact p != 0;
            fact p == identity;
            fact rest.model == rest_model;
        },
    }
}

function chain_rest(chain: Chain) -> Chain {
    match chain {
        Chain::End => Chain::End,
        Chain::Link(identity, rest) => rest,
    }
}

int chain_has_next(struct node* p) {
    owns c: chain_at(p);
    requires c.model != Chain::End;
    ensures c.model == old(c.model);
    ensures c.model == Chain::Link(p, chain_rest(old(c.model)));
} by {
    match c.model {
        Chain::End => { contradiction(c.model == Chain::End); },
        Chain::Link(identity, rest_model) => {
            unfold(c) as { rest: n };
            branch {
                then { step(); simp(); }
                else {}
            }
            branch {
                then {
                    step();
                    let c = fold(chain_at(p), { model: old(c.model) }, { rest: n });
                    have chain_rest(old(c.model)) == rest_model by {
                        rewrite(old(c.model) == Chain::Link(identity, rest_model));
                        unfold(chain_rest(Chain::Link(identity, rest_model)));
                        normalize();
                    }
                    have c.model == Chain::Link(p, chain_rest(old(c.model))) by {
                        rewrite(chain_rest(old(c.model)) == rest_model);
                        rewrite(p == identity);
                        simp();
                    }
                    simp();
                }
                else {}
            }
            step();
            let c = fold(chain_at(p), { model: old(c.model) }, { rest: n });
            have chain_rest(old(c.model)) == rest_model by {
                rewrite(old(c.model) == Chain::Link(identity, rest_model));
                unfold(chain_rest(Chain::Link(identity, rest_model)));
                normalize();
            }
            have c.model == Chain::Link(p, chain_rest(old(c.model))) by {
                rewrite(chain_rest(old(c.model)) == rest_model);
                rewrite(p == identity);
                simp();
            }
            simp();
        },
    }
}
```

```expect
pass
```
