# A fresh heap parent's link is read through its named resource

A caller allocates a parent, links a child through `parent_attach`, and hands
the named `parent(p)` resource to `parent_detach`, whose body reads `p->kid`
before freeing the parent. At the call, the caller's raw heap cell is still
uninitialized: the store happened inside the attach call and is held by the
named resource's `Linked(kid)` arm. The call must take the read's value from
that selected constructor binding instead of reporting an uninitialized read,
and the named instance passes through the call's population transfer
unchanged. This catches a direct call that rejects a callee read covered by a
named resource arm.

The logical pointer annotations below use `void*` for address identities;
object access remains governed by the unchanged C types and resource ownership.

```c filename=fresh_heap_parent_link.c
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
verifying "fresh_heap_parent_link.c";
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
    step(parent_detach, { link: link });
    step();
    close();
}
```

```expect
pass
```
