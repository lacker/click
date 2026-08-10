# Invariant-bearing resource populations authorize their body

An opaque call may produce a wrapper whose body owns C memory and states a
fact about that memory. A scoped `open` uses the population's one active body,
restores its fact after a store, and leaves the refreshed body available for a
later opaque consumer.

```c filename=invariant_population_wrap.c
struct object {
    int32 field;
};

void wrap_object(struct object* obj) {
}
```

```c filename=invariant_population_unwrap.c
struct object {
    int32 field;
};

void unwrap_object(struct object* obj) {
}
```

```c filename=invariant_population_restore.c
struct object {
    int32 field;
};

void restore_wrapper_invariant(struct object* obj) {
    obj->field = 7;
}
```

```c filename=invariant_population_body_access.c
struct object {
    int32 field;
};

void write_through_wrapper(struct object* obj) {
    wrap_object(obj);
    restore_wrapper_invariant(obj);
    obj->field = 7;
    unwrap_object(obj);
}
```

```click
resource wrapper(obj: struct object*) {
    owns object(obj);
    fact obj->field == 7;
}

verifying "invariant_population_wrap.c";
verifying "invariant_population_unwrap.c";
verifying "invariant_population_restore.c";
verifying "invariant_population_body_access.c";

void wrap_object(struct object* obj) {
    requires obj->field == 7;
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

void restore_wrapper_invariant(struct object* obj) {
    owns wrapper(obj);
    mutable obj->field;
} by {
    open(wrapper(obj)) {
        execute();
        frame();
        simp();
    }
}

void write_through_wrapper(struct object* obj) {
    requires obj->field == 7;
    owns object(obj);
    mutable obj->field;
} by {
    step();
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
