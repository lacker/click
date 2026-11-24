# A retaining call cannot turn a cached value into an arbitrary result

An ordinary control owns the counter cell and reference-family authority.
The retaining helper updates the cell and explicitly creates one member before
returning the restored control. The caller reads and closes its control before
the call; its cached local denotes the pre-call value, while the restored
control describes the post-call counter and count. Neither fact proves the
false `result == 12345` claim. The C source is unchanged.

```c filename=population_call_cached_body.c
struct object {
    int32 refs;
};

struct object* object_retain(struct object* obj) {
    obj->refs = obj->refs + 1;
    return obj;
}

int32 caller(struct object* obj) {
    int32 before;
    before = obj->refs;
    object_retain(obj);
    return before;
}
```

```click
authorized resource object_ref(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(object_ref(obj));
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "population_call_cached_body.c";

struct object* object_retain(struct object* obj) {
    requires count(object_ref(obj)) < 2147483647;
    owns control(obj);
    produces object_ref(obj);
    ensures result == obj;
} by {
    with(control(obj)) {
        step();
        fold(object_ref(obj));
        step_until(function.exit);
    }
    close();
}

int32 caller(struct object* obj) {
    requires count(object_ref(obj)) < 2147483647;
    owns control(obj);
    produces object_ref(obj);
    ensures result == 12345;
} by {
    with(control(obj)) {
        step();
        step();
    }
}
```

```expect
fail: `ensures result == 12345` failed
```
