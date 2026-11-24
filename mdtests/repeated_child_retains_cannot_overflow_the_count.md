# Repeated retains cannot overflow the population count

The entry bound permits the first retain. It does not permit a second one:
if the initial count is `2147483646`, the first call raises it to
`2147483647`, violating the next call's strict upper bound. Require the
precondition refusal at tactic 1 (the second call), rather than a later
failure while constructing returned resources.

```c filename=retain.c
struct child {
    int32 refs;
    int32 payload;
};

void child_retain(struct child* obj) {
    obj->refs = obj->refs + 1;
}

void retain_many(struct child* obj) {
    child_retain(obj);
    child_retain(obj);
    child_retain(obj);
    child_retain(obj);
}
```

```click
authorized resource child_ref(obj: struct child*) {}

resource child_storage(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
}

resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact defined(obj->refs);
    fact defined(obj->payload);
    fact obj->refs == count(child_ref(obj));
}

verifying "retain.c";

void child_retain(struct child* obj) {
    requires count(child_ref(obj)) < 2147483647;
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

void retain_many(struct child* obj) {
    requires count(child_ref(obj)) < 2147483647;
    owns child_control(obj);
    owns child_ref(obj);
    produces child_ref(obj);
    produces child_ref(obj);
    produces child_ref(obj);
    produces child_ref(obj);
} by {
    step(child_retain);
    step(child_retain);
    step(child_retain);
    step(child_retain);
    step();
    close();
}
```

```expect
fail: `retain_many.contract` tactic 1: `step()` requires an explicit prerequisite proof (precondition clause 1 of `child_retain`)
```
