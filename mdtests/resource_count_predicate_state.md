# Predicates capture resource-count states

A predicate containing `count(...)` describes the resource state captured
when the predicate was established. After a retain transition, the proof must
establish a fresh predicate for the new memory and population count.

```c filename=resource_count_predicate_state.c
struct object {
    int32 refs;
};

struct object* object_retain(struct object* obj) {
    obj->refs = obj->refs + 1;
    return obj;
}
```

```click
authorized resource object_ref(obj: struct object*) {}
resource control(obj: struct object*) {
    owns obj->refs;
    owns authority(object_ref(obj));
    fact obj->refs == count(object_ref(obj));
}

predicate valid_refcount(obj: struct object*) {
    obj->refs == count(object_ref(obj))
}

verifying "resource_count_predicate_state.c";

struct object* object_retain(struct object* obj) {
    requires count(object_ref(obj)) < 2147483647;
    requires valid_refcount(obj);
    owns control(obj);
    owns object_ref(obj);
    produces object_ref(obj);

    ensures valid_refcount(obj);
    ensures result == obj;
} by {
    open(control(obj)) {
        unfold(valid_refcount);
        step();
        fold(object_ref(obj));
        have valid_refcount(obj) by {
            unfold(valid_refcount);
            solve();
        }
    }
}
```

```expect
pass
```
