# Leak diagnostics name the declared obligation and its surface pointer

The allocation-lifetime diagnostic should identify the declared resource that
keeps an allocation live. A pointer loaded from a struct field should use the
field's C spelling instead of exposing lowered memory-block and load terms.

```c filename=shared_heap_detach_leak_diagnostic.c
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

verifying "shared_heap_detach_leak_diagnostic.c";

void child_release_nonfinal(struct child* obj) {
    requires 1 <= obj->refs;
    owns child_control(obj);
    consumes child_ref(obj);
} by {
    unfold(child_control(obj));
    unfold(child_ref(obj));
    have to_integer(obj->refs - 1) >= 0;
    step();
    fold(child_control(obj));
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    requires to_integer(count(child_ref(p->kid))) == 1;
    consumes child_control(p->kid);
    consumes child_ref(p->kid);
    produces out: parent(p);
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(entry_child) => {
            unfold(link);
            step_until(statement(1).entry);
            step(child_release_nonfinal);
            unfold(child_control(kid));
            unfold(authority(child_ref(kid)));
            step_until(function.exit);
            let out = fold(parent(p), { link: ParentLink::Empty });
            close();
        },
    }
}
```

```expect
fail: live allocation obligation was neither returned nor freed: `owns allocation(old(p->kid), 8)`
```
