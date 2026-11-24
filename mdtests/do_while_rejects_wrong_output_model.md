# A loop cannot invent a different output model
```c filename=walk.c
struct Node { struct Node *next; };
void walk(struct Node *p, int *marker) {
    do { p = p->next; } while (p);
    *marker = 7;
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
resource path(p: struct Node*) {
    field model: Path;
    match model {
        Path::Top => { },
        Path::Step(identity, before) => {
            owns identity->next;
            owns up: path(identity);
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
    produces whole: path(0);
    produces empty: list(0);
    ensures whole.model == Path::Top;
    ensures marker[0] == 7;
} by {
    let c = fold(path(p), { model: Path::Top });
    loop {
        owns t: list(p);
        owns c: path(p);
        decreases t;
        invariant p != 0;
        initialize by close();
        maintain by {
            match t.model {
                Chain::Empty => { unfold(t); contradiction(p == 0); },
                Chain::Node(identity, rest) => {
                    let { tail: next } = unfold(t);
                    let frame = fold(path(p->next), { model: Path::Step(identity, c.model), up: c });
                    step();
                    if p == 0 {
                    } else {
                    }
                },
            }
        }
    }
    have c.model != Path::Top by normalize();
    match c.model {
        Path::Top => { contradiction(c.model == Path::Top); },
        Path::Step(identity, before) => {
            let { up: above } = unfold(c);
            have p == 0 by close();
            have identity != 0;
            let whole = fold(path(p), { model: Path::Step(identity, before), up: above });
            match t.model {
                Chain::Empty => {
                    unfold(t);
                    let empty = fold(list(0), { model: Chain::Empty });
                    step_until(function.exit); close();
                },
                Chain::Node(next_identity, rest) => {
                    have t.model != Chain::Empty by {
                        rewrite(t.model, Chain::Node(next_identity, rest)); normalize();
                    }
                    contradiction(t.model == Chain::Empty);
                },
            }
        },
    }
}
```
```expect
fail: unclosed goal: whole.model == Path::Top()
```
