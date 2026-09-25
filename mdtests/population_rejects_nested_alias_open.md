# A second membership cannot reopen a suspended population body

A scoped `open` exposes the one body owned by an active population. It does
not consume a unit, and closing the block requires every body resource to be
restored.

```c filename=resource_population_open.c
struct object {
    int32 refs;
};

int32 object_refcount(struct object* obj, struct object* alias) {
    return obj->refs;
}
```

```click
resource object_ref(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "resource_population_open.c";

int32 object_refcount(struct object* obj, struct object* alias) {
    owns object_ref(obj);
    requires alias == obj;

    ensures result == count(object_ref(obj));
} by {
    open(object_ref(obj)) {
        open(object_ref(alias)) { execute(); }
    }
    simp();
}
```

```expect
fail: population body is already open
```
