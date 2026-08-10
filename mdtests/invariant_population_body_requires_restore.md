# Closing an invariant-bearing population requires restoring its fact

The active population body is authoritative, not an excuse to retain a stale
fact after mutation. Closing `open` fails when the body invariant is false at
the new C-memory snapshot.

```c filename=invariant_population_restore_wrap.c
struct object {
    int32 field;
};

void wrap_object(struct object* obj) {
}
```

```c filename=invariant_population_break.c
struct object {
    int32 field;
};

void break_wrapper_invariant(struct object* obj) {
    wrap_object(obj);
    obj->field = 8;
}
```

```click
resource wrapper(obj: struct object*) {
    owns object(obj);
    fact obj->field == 7;
}

verifying "invariant_population_restore_wrap.c";
verifying "invariant_population_break.c";

void wrap_object(struct object* obj) {
    requires obj->field == 7;
    consumes object(obj);
    produces wrapper(obj);
} by {
    execute();
    fold(wrapper(obj));
    simp();
}

void break_wrapper_invariant(struct object* obj) {
    requires obj->field == 7;
    owns object(obj);
    mutable obj->field;
} by {
    step();
    open(wrapper(obj)) {
        step();
    }
    execute();
}
```

```expect
fail: requires an exact body fact
```
