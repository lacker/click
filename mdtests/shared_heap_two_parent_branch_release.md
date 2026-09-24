# `parent_detach` loses the child reference invariant across `child_release`

The creator owns one counted child reference, each attached parent adds one,
and the creator releases its reference before either parent detaches.  The
first detach should consume one `child_ref` while leaving the child's counted
population nonempty; the second should consume the final reference and free
the child. Before the allocation-lifetime check can decide that, contract
certification fails while re-establishing `child_ref`'s invariant
`obj->refs == count(child_ref(obj))` after the modular `child_release` call.
The call contract states the count delta, but does not expose the matching
refcount update on the branch where the allocation survives.

```c filename=shared_heap_two_parent_branch_release.c
struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

void child_retain(struct child* obj) {
    obj->refs = obj->refs + 1;
}

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}

void parent_attach(struct parent* p, struct child* kid) {
    p->kid = kid;
    child_retain(kid);
}

int32 parent_read_payload(struct parent* p) {
    struct child* kid = p->kid;
    return kid->payload;
}

void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release(kid);
    p->kid = 0;
}

void caller(struct parent* first, struct parent* second, struct child* kid) {
    parent_attach(first, kid);
    parent_attach(second, kid);
    child_release(kid);
    parent_detach(first);
    int32 observed = parent_read_payload(second);
    parent_detach(second);
}
```

```click
spec enum ParentLink {
    Empty,
    Linked(struct child*),
}

resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => {},
        ParentLink::Linked(kid) => {
            owns &p->kid;
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

resource child_ref(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    fact obj->refs == count(child_ref(obj));
}

verifying "shared_heap_two_parent_branch_release.c";

void child_retain(struct child* obj) {
    requires count(child_ref(obj)) < 2147483647;
    owns child_ref(obj);
    produces child_ref(obj);
} by {
    open(child_ref(obj)) {
        execute();
    }
    simp();
}

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_ref(obj);
    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;
} by {
    if obj->refs == 1 {
        unfold(child_ref(obj));
        execute();
        simp();
    } else {
        open(child_ref(obj)) {
            execute();
        }
        have 1 < old(obj->refs) by {
            arithmetic() using {
                1 <= old(obj->refs);
                old(obj->refs) != 1;
            }
        }
        have old(obj->refs) - 1 >= 1 by {
            apply(int32_above_one_predecessor_is_at_least_one(old(obj->refs))) using {
                1 < old(obj->refs);
            }
        }
        have old(obj->refs) == old(count(child_ref(obj))) by { simp(); }
        have old(count(child_ref(obj))) > 1 by {
            simp() using {
                old(obj->refs) > 1;
                old(obj->refs) == old(count(child_ref(obj)));
            }
        }
        have count(child_ref(obj)) != 0 by {
            arithmetic() using { old(count(child_ref(obj))) > 1; }
        }
        simp();
    }
}

void parent_attach(struct parent* p, struct child* kid) {
    requires count(child_ref(kid)) < 2147483647;
    requires kid != 0;
    consumes &p->kid;
    owns child_ref(kid);
    produces child_ref(kid);
    produces link: parent(p);
    ensures link.link == ParentLink::Linked(kid);
} by {
    execute();
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    simp();
}

int32 parent_read_payload(struct parent* p) {
    owns link: parent(p);
    requires link.link != ParentLink::Empty;
    owns child_ref(p->kid);
    ensures result == p->kid->payload;
    ensures result == old(p->kid->payload);
    ensures p->kid == old(p->kid);
    ensures link.link == ParentLink::Linked(old(p->kid));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            open(child_ref(p->kid)) { execute(); }
            let link = fold(parent(p), { link: ParentLink::Linked(p->kid) });
            simp();
        },
    }
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    consumes child_ref(p->kid);
    produces out: parent(old(p));
    ensures count(child_ref(old(p->kid))) == old(count(child_ref(p->kid))) - 1;
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            have old(p->kid) == kid by simp;
            execute();
            let out = fold(parent(p), { link: ParentLink::Empty });
            simp();
        },
    }
}

void caller(struct parent* first, struct parent* second, struct child* kid) {
    consumes &first->kid;
    consumes &second->kid;
    requires kid != 0;
    owns child_ref(kid);
} by {
    let { link: first_link } = step(parent_attach(first, kid), {});
    have count(child_ref(kid)) == 2 by simp;
    let { link: second_link } = step(parent_attach(second, kid), {});
    have count(child_ref(kid)) == 3 by simp;
    step(child_release(kid), {});
    have count(child_ref(kid)) == 2 by simp;
    let first_out = step(parent_detach(first), { link: first_link });
    step();
    have count(child_ref(kid)) == 2 by simp;
    step(parent_read_payload(second), { link: second_link });
    let second_out = step(parent_detach(second), { link: second_link });
    step();
    simp();
}
```

```expect
fail: could not prove `fact obj->refs == count(child_ref(obj));` of resource `child_ref`
```
