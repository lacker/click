# An ordinary control cannot be opened twice

Scoped opening exposes exclusive counter memory and authority. The same
control cannot supply that body to a second nested opening.

```c filename=resource_population_open.c
struct object {
    int32 refs;
};

int32 object_refcount(struct object* obj) {
    return obj->refs;
}
```

```click
authorized resource object_ref(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(object_ref(obj));
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "resource_population_open.c";

int32 object_refcount(struct object* obj) {
    owns control(obj);

    ensures result == count(object_ref(obj));
} by {
    with(control(obj)) {
        with(control(obj)) { }
    }
    close();
}
```

```expect
fail: population body is already open
```
