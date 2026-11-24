# A pure tautology preserves population certification

The C source is the frozen shared-parent probe, unchanged. Adding a pure
tautology to detach must still certify the child population after the
disjoint parent-link store.

```c filename=shared_parent.c
struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

void child_init(struct child* obj, int32 payload) {
    obj->refs = 1;
    obj->payload = payload;
}

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

int32 run_first_destroyed(int32 payload) {
    struct child* kid = malloc(sizeof(struct child));
    if (kid == 0) {
        return -1;
    }
    child_init(kid, payload);
    struct parent* first = malloc(sizeof(struct parent));
    if (first == 0) {
        child_release(kid);
        return -1;
    }
    struct parent* second = malloc(sizeof(struct parent));
    if (second == 0) {
        child_release(kid);
        free(first);
        return -1;
    }
    parent_attach(first, kid);
    parent_attach(second, kid);
    child_release(kid);
    parent_detach(first);
    int32 out = parent_read_payload(second);
    parent_detach(second);
    free(first);
    free(second);
    return out;
}

int32 run_second_destroyed(int32 payload) {
    struct child* kid = malloc(sizeof(struct child));
    if (kid == 0) {
        return -1;
    }
    child_init(kid, payload);
    struct parent* first = malloc(sizeof(struct parent));
    if (first == 0) {
        child_release(kid);
        return -1;
    }
    struct parent* second = malloc(sizeof(struct parent));
    if (second == 0) {
        child_release(kid);
        free(first);
        return -1;
    }
    parent_attach(first, kid);
    parent_attach(second, kid);
    child_release(kid);
    parent_detach(second);
    int32 out = parent_read_payload(first);
    parent_detach(first);
    free(first);
    free(second);
    return out;
}
```

```click
import click::integer;

spec enum ParentLink {
    Empty,
    Linked(struct child*),
}

resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => {
            owns p->kid;
            fact defined(p->kid);
            fact p->kid == 0;
        },
        ParentLink::Linked(kid) => {
            owns p->kid;
            fact defined(p->kid);
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

authorized resource child_ref(obj: struct child*) {}

resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact defined(obj->refs);
    fact defined(obj->payload);
    fact to_integer(obj->refs) == to_integer(count(child_ref(obj)));
}

resource child_storage(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
}

verifying "shared_parent.c";

void child_init(struct child* obj, int32 payload) {
    requires to_integer(count(child_ref(obj))) == 0;
    owns child_storage(obj);
    produces child_ref(obj);
    ensures obj->refs == 1;
    ensures defined(obj->refs);
    ensures defined(obj->payload);
    ensures obj->payload == payload;
} by {
    unfold(child_storage(obj));
    step();
    step();
    fold(child_ref(obj));
    fold(child_storage(obj));
}

void child_retain(struct child* obj) {
    requires to_integer(count(child_ref(obj))) < 2147483647;
    owns child_control(obj);
    owns child_ref(obj);
    produces child_ref(obj);
    ensures obj->payload == old(obj->payload);
} by {
    unfold(child_control(obj));
    step();
    fold(child_ref(obj));
    fold(child_control(obj));
}

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_control(obj);
    consumes child_ref(obj);
    if old(obj->refs) > 1 {
        produces child_control(obj);
    }
    ensures to_integer(count(child_ref(obj))) == to_integer(old(count(child_ref(obj))) - 1);
    ensures to_integer(old(count(child_ref(obj)))) > 1 implies obj->payload == old(obj->payload);
} by {
    unfold(child_control(obj));
    if obj->refs == 1 {
        unfold(child_ref(obj));
        unfold(authority(child_ref(obj)));
        step_until(function.exit);
        close();
    } else {
        unfold(child_ref(obj));
        have 1 < obj->refs by {
            close() using { 1 <= obj->refs; obj->refs != 1; };
        }
        have to_integer(obj->refs - 1) >= 1;
        step();
        step();
        fold(child_control(obj));
        step_until(function.exit);
        close();
    }
}

void parent_attach(struct parent* p, struct child* kid) {
    requires to_integer(count(child_ref(kid))) < 2147483647;
    requires kid != 0;
    requires separate(memory(p->kid), memory(kid->payload));
    consumes p->kid;
    owns child_control(kid);
    owns child_ref(kid);
    produces child_ref(kid);
    produces link: parent(p);
    ensures link.link == ParentLink::Linked(kid);
    ensures kid->payload == old(kid->payload);
} by {
    step_until(function.exit);
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    close();
}

int32 parent_read_payload(struct parent* p) {
    owns link: parent(p);
    requires link.link != ParentLink::Empty;
    owns child_control(p->kid);
    owns child_ref(p->kid);
    ensures result == p->kid->payload;
    ensures result == old(p->kid->payload);
    ensures p->kid == old(p->kid);
    ensures link.link == old(link.link);
    ensures link.link == ParentLink::Linked(old(p->kid));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(linked_child) => {
            unfold(link);
            have old(p->kid) == linked_child;
            with(child_control(p->kid)) { step_until(function.exit); }
            let link = fold(parent(p), { link: ParentLink::Linked(linked_child) });
            close();
        },
    }
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    requires 1 <= p->kid->refs;
    consumes child_control(p->kid);
    consumes child_ref(p->kid);
    if to_integer(old(count(child_ref(p->kid)))) > 1 {
        produces child_control(old(p->kid));
    }
    produces p->kid;
    ensures old(p->kid) == old(p->kid);
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(linked_child) => {
            unfold(link);
            have old(p->kid) == linked_child;
            have to_integer(old(p->kid->refs)) == to_integer(old(count(child_ref(p->kid))));
            step();
            have linked_child->refs == old(p->kid->refs);
            if linked_child->refs > 1 {
                have to_integer(old(count(child_ref(p->kid)))) > 1;
                step_until(function.exit);
                close();
            } else {
                have to_integer(old(count(child_ref(p->kid)))) == to_integer(linked_child->refs);
                have to_integer(old(count(child_ref(p->kid)))) <= 1 by {
                    rewrite(to_integer(old(count(child_ref(p->kid)))), to_integer(linked_child->refs));
                    close();
                }
                step_until(function.exit);
                close();
            }
        },
    }
}
```

```expect
pass
```
