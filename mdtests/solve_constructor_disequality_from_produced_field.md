# solve proves a constructor disequality from a call-produced field

`parent_attach` produces the instance `link` and ensures
`link.link == ParentLink::Linked(kid)`. `solve` proves
`link.link != ParentLink::Empty` from it: synthesis spells the produced
field and the constructor, the equality rewrites the goal, and
normalization decides the two constructors differ. The same reasoning lets
the implicit closer prove `parent_detach`'s precondition on its call step.

The logical pointer annotations below use `void*` for address identities;
object access remains governed by the unchanged C types and resource ownership.

```c filename=solve_constructor_disequality_from_produced_field.c
struct child { int32 refs; };
struct parent { struct child* kid; };
void parent_attach(struct parent* p, struct child* kid) {
    p->kid = kid;
}
struct child* parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    free(p);
    return kid;
}
int32 adopt(struct child* kid) {
    struct parent* p = malloc(sizeof(struct parent));
    if (p == 0) { return -1; }
    parent_attach(p, kid);
    parent_detach(p);
    return 0;
}
```

```click
spec enum ParentLink {
    Empty,
    Linked(void*),
}
resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => { owns p->kid; },
        ParentLink::Linked(kid) => {
            owns p->kid;
            fact p->kid == kid;
        },
    }
}
verifying "solve_constructor_disequality_from_produced_field.c";
void parent_attach(struct parent* p, struct child* kid) {
    consumes uninitialized(p->kid);
    produces link: parent(p);
    ensures link.link == ParentLink::Linked(kid);
} by {
    step();
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
}
struct child* parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    consumes allocation(p, sizeof(struct parent));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(linked) => {
            unfold(link);
            step_until(function.exit);
            close();
        },
    }
}
int32 adopt(struct child* kid) {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch {
        true => {
            step();
            close();
        }
        false => {}
    }
    let { link: link } = step(parent_attach);
    have link.link != ParentLink::Empty by close();
    step(parent_detach, { link: link });
    step();
    close();
}
```

```expect
pass
```
