# resource-population retain and nonfinal release

Producing or consuming one resource unit changes the population count. The
stored count must be updated by the same amount before Click will return the
new resource context.

```c filename=counted_resource_retain.c
struct object {
    int32 refs;
};

struct object* object_retain(struct object* obj) {
    obj->refs = obj->refs + 1;
    return obj;
}
```

```c filename=counted_resource_release.c
struct object {
    int32 refs;
};

void object_release_nonfinal(struct object* obj) {
    obj->refs = obj->refs - 1;
}
```

```click
resource object_ref(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "counted_resource_retain.c";
verifying "counted_resource_release.c";

struct object* object_retain(struct object* obj) {
    requires count(object_ref(obj)) < 2147483647;
    owns object_ref(obj);
    produces object_ref(obj);
    mutable obj->refs;

    ensures result == obj;
} by {
    open(object_ref(obj)) {
        execute();
        frame();
    }
    simp();
}

void object_release_nonfinal(struct object* obj) {
    requires 1 < count(object_ref(obj));
    owns object_ref(obj);
    consumes object_ref(obj);
    mutable obj->refs;
} by {
    open(object_ref(obj)) {
        execute();
        frame();
    }
    simp();
}
```

```expect
pass
```
