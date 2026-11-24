# A pre-loop fold does not make a returning loop path vacuous
```c filename=walk.c
struct Node { struct Node *next; };
struct Node *walk(struct Node *p, int *marker) {
    do { p = p->next; return p; } while (p);
    return p;
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
struct Node* walk(struct Node* p, int32* marker) {
    consumes t: list(p);
    owns marker[0];
    requires p != 0;
    requires marker[0] == 9;
    produces whole: path(result);
    produces remaining: list(result);
    ensures whole.model == Path::Top;
    ensures marker[0] == 9;
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
                    let { tail: remaining } = unfold(t);
                    let whole = fold(path(p->next), { model: Path::Step(identity, c.model), up: c });
                    step();
                    step();
                },
            }
        }
    }
    close();
}
```
```expect
fail: unclosed goal: whole.model == Path::Top()
```
