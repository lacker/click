# Predicates capture resource-count snapshots

A predicate containing `count(...)` describes the resource snapshot captured
when the predicate was established. After a retain transition, the proof must
establish a fresh predicate for the new memory and population count.

```c filename=resource_count_predicate_snapshot.c
struct object {
    int32 refs;
};

struct object* object_retain(struct object* obj) {
    obj->refs = obj->refs + 1;
    return obj;
}
```

```click
resource object_ref(obj: struct object*) {
    owns obj->refs;
}

predicate valid_refcount(obj: struct object*) {
    obj->refs == count(object_ref(obj))
}

verifying "resource_count_predicate_snapshot.c";

struct object* object_retain(struct object* obj) {
    requires count(object_ref(obj)) < 2147483647;
    requires valid_refcount(obj);
    owns object_ref(obj);
    produces object_ref(obj);
    mutable obj->refs;

    ensures valid_refcount(obj);
    ensures result == obj;
} by {
    open(object_ref(obj)) {
        unfold(valid_refcount);
        execute();
        frame();
        have valid_refcount(obj) by {
            unfold(valid_refcount);
            simp();
        }
    }
    simp();
}
```

```expect
pass
```
