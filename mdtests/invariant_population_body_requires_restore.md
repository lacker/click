# Closing an invariant-bearing population requires restoring its fact

The active population body is authoritative, not an excuse to retain a stale
fact after mutation. Closing `with` fails when the body invariant is false at
the new C-memory state.

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
    owns *obj;
    fact obj->field == 7;
}

verifying "invariant_population_restore_wrap.c";
verifying "invariant_population_break.c";

void wrap_object(struct object* obj) {
    requires obj->field == 7;
    consumes *obj;
    produces wrapper(obj);
} by {
    step_until(function.exit);
    fold(wrapper(obj));
    close();
}

void break_wrapper_invariant(struct object* obj) {
    requires obj->field == 7;
    owns *obj;
} by {
    step();
    with(wrapper(obj)) {
        step();
    }
}
```

```expect
fail: requires an exact body fact
```
