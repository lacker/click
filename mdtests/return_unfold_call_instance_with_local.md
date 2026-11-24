# A call-produced instance unfolds after return and local retirement

```c filename=s.c
struct node { struct node* left; };
struct root { struct node* top; };

void relink(struct root* r, struct node* n) {
    r->top = n;
}

int32 pick(struct root* r, struct node* n) {
    struct node* t = n;
    relink(r, t);
    return 0;
}
```

```click
spec enum Ctx { Top, Other }
resource at(child: struct node*, r: struct root*) {
    field model: Ctx;
    match model {
        Ctx::Top => {
            owns r->top;
            fact r != 0;
            fact r->top == child;
        },
        Ctx::Other => {
            owns r->top;
        },
    }
}
resource out(r: struct root*) {
    field model: int32;
    owns r->top;
    fact r != 0;
}
verifying "s.c";
void relink(struct root* r, struct node* n) {
    consumes before: at(0, r);
    requires before.model == Ctx::Top;
    produces after: at(n, r);
    ensures after.model == Ctx::Top;
} by {
    unfold(before);
    step_until(function.exit);
    let after = fold(at(n, r), { model: Ctx::Top });
    close();
}
int32 pick(struct root* r, struct node* n) {
    consumes c: at(0, r);
    requires c.model == Ctx::Top;
    produces o: out(r);
    ensures o.model == 0;
} by {
    step();
    step();
    let { after: c } = step(relink, { before: c });
    step_until(function.exit);
    unfold(c);
    let o = fold(out(r), { model: 0 });
    close();
}
```
```expect
pass
```
