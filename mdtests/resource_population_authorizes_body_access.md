# Resource populations authorize their owned bodies during C execution

An opaque call may exchange a raw object for a declared wrapper resource. A
scoped `open` exposes that same ownership to the following C store, and a
second opaque call can consume the closed wrapper and return the raw object.

```c filename=resource_population_wrap.c
struct object {
    int32 field;
};

void wrap_object(struct object* obj) {
}
```

```c filename=resource_population_unwrap.c
struct object {
    int32 field;
};

void unwrap_object(struct object* obj) {
}
```

```c filename=resource_population_body_access.c
struct object {
    int32 field;
};

void write_through_wrapper(struct object* obj) {
    wrap_object(obj);
    obj->field = 7;
    unwrap_object(obj);
}
```

```click
resource wrapper(obj: struct object*) {
    owns object(obj);
}

verifying "resource_population_wrap.c";
verifying "resource_population_unwrap.c";
verifying "resource_population_body_access.c";

void wrap_object(struct object* obj) {
    consumes object(obj);
    produces wrapper(obj);
} by {
    execute();
    fold(wrapper(obj));
    simp();
}

void unwrap_object(struct object* obj) {
    consumes wrapper(obj);
    produces object(obj);
} by {
    unfold(wrapper(obj));
    execute();
    simp();
}

void write_through_wrapper(struct object* obj) {
    owns object(obj);
    mutable obj->field;
} by {
    step();
    open(wrapper(obj)) {
        step();
    }
    step();
    execute();
    frame();
    simp();
}
```

```expect
pass
```
