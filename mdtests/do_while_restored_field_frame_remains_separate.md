# A reconstructed field at a nonzero offset stays separate from the caller frame
The path resource keeps the saved pointer as an argument. Opening the
restored frame establishes that its node is the one the C local `q`
still names.

```c filename=walk.c
struct Node { int padding; struct Node *next; };
void walk(struct Node *p, int *marker) {
    struct Node *q = p;
    do { p = p->next; break; } while (p);
    q->next = 0;
}
```
```click
verifying "walk.c";
spec enum Chain { Empty, Node(struct Node*, Chain), }
spec enum Path { Top, Step(struct Node*, Path), }
resource list(p: struct Node*) {
    field model: Chain;
    match model {
        Chain::Empty => { fact p == 0; },
        Chain::Node(identity, rest) => {
            owns p->next;
            owns tail: list(p->next);
            fact p != 0;
            fact p == identity;
            fact tail.model == rest;
        },
    }
}
resource path(p: struct Node*, saved: struct Node*) {
    field model: Path;
    match model {
        Path::Top => { },
        Path::Step(identity, before) => {
            owns identity->next;
            owns up: path(identity, saved);
            fact identity == saved;
            fact identity != 0;
            fact identity->next == p;
            fact up.model == before;
        },
    }
}
void walk(struct Node* p, int32* marker) {
    consumes t: list(p);
    owns marker[0];
    requires p != 0;
    requires marker[0] == 9;
    ensures marker[0] == 9;
} by {
    step(); step();
    let c = fold(path(p, q), { model: Path::Top });
    loop {
        owns t: list(p);
        owns c: path(p, q);
        decreases t;
        invariant p != 0;
        invariant p == q;
        initialize by close();
        maintain by {
            match t.model {
                Chain::Empty => { unfold(t); contradiction(p == 0); },
                Chain::Node(identity, rest) => {
                    let { tail: next } = unfold(t);
                    let frame = fold(path(p->next, q), { model: Path::Step(identity, c.model), up: c });
                    step();
                    step();
                },
            }
        }
    }
    have c.model != Path::Top by close();
    match c.model {
        Path::Top => { contradiction(c.model == Path::Top); },
        Path::Step(identity, before) => {
            let { up: previous } = unfold(c);
            have q == identity;
            have separate(memory(marker[0]), memory(identity->next));
            have marker[0] == 9;
            have separate(memory(identity->next), memory(marker[0])) by {
                apply(click::separation::separate_symm(memory(marker[0]), memory(identity->next)));
            }
            have separate(memory(q->next), memory(marker[0])) by {
                rewrite(q, identity);
                close();
            }
            mark before_store;
            step();
            have separate(statement(2).footprint, memory(marker[0])) by {
                close() using { at(before_store, separate(memory(q->next), memory(marker[0]))); };
            }
            have marker[0] == at(before_store, marker[0]) by {
                preserve(memory(marker[0]), statement(2));
            }
            have marker[0] == 9 by { close(); }
            step_until(function.exit); close();
        },
    }
}
```
```expect
pass
```
