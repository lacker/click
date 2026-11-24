# Conditional entry-state resource arguments remain valid at function exit

The `owns child_ref(p->kid)` clause already returns the borrowed survivor.
The detach contract consumes its additional member and does not also promise
a duplicate produced member after clearing the field.

```c filename=shared_heap_detach_old_resource_handoff.c
struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

void child_release_nonfinal(struct child* obj) {
    obj->refs = obj->refs - 1;
}

void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release_nonfinal(kid);
    p->kid = 0;
}
```

```click
import click::integer;

spec enum ParentLink {
    Empty,
    Linked(struct child*),
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

resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => {},
        ParentLink::Linked(kid) => {
            owns p->kid;
            fact defined(p->kid);
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

verifying "shared_heap_detach_old_resource_handoff.c";

void child_release_nonfinal(struct child* obj) {
    requires 1 < obj->refs;
    owns child_control(obj);
    owns child_ref(obj);
    consumes child_ref(obj);
} by {
    unfold(child_control(obj));
    unfold(child_ref(obj));
    have 1 < obj->refs;
    have to_integer(obj->refs - 1) >= 1;
    step();
    fold(child_control(obj));
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    requires 1 < to_integer(count(child_ref(p->kid)));
    consumes child_control(p->kid);
    if to_integer(old(count(child_ref(p->kid)))) > 1 {
        produces child_control(old(p->kid));
    }
    owns child_ref(p->kid);
    consumes child_ref(p->kid);
    produces out: parent(old(p));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(entry_child) => {
            unfold(link);
            step_until(function.exit);
            let out = fold(parent(p), { link: ParentLink::Empty });
            close();
        },
    }
}
```

```expect
pass
```
