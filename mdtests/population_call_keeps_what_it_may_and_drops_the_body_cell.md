# Population calls: what the caller keeps and what it re-reads

Positive controls for `call_inside_open_population_does_not_assume_its_body.md`
and `population_call_drops_the_cached_body_cell.md`.

`restore_around_a_call` holds `object_ref(obj)` open across an unrelated call
and restores the count cell before closing: its own stores survive the call,
which writes nothing the caller owns, so the close proves the body fact from
them without the call assuming it. `count_before_retain` reads the count cell,
closes the body, and calls `object_retain`; the post-call body fact names the
re-read cell at the new count, and the value read before the call is the
pre-call count.

```c filename=population_call_controls.c
struct object {
    int32 refs;
};

int32 three() {
    return 3;
}

struct object* object_retain(struct object* obj) {
    obj->refs = obj->refs + 1;
    return obj;
}

int32 restore_around_a_call(struct object* obj) {
    int32 saved;
    saved = obj->refs;
    obj->refs = 0;
    three();
    obj->refs = saved;
    return saved;
}

int32 count_before_retain(struct object* obj) {
    int32 before;
    before = obj->refs;
    object_retain(obj);
    return before;
}
```

```click
resource object_ref(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "population_call_controls.c";

int32 three() {
    ensures result == 3;
} by auto;

struct object* object_retain(struct object* obj) {
    requires count(object_ref(obj)) < 2147483647;
    owns object_ref(obj);
    produces object_ref(obj);
    ensures result == obj;
} by {
    open(object_ref(obj)) {
        execute();
    }
    simp();
}

int32 restore_around_a_call(struct object* obj) {
    owns object_ref(obj);
    ensures result == count(object_ref(obj));
} by {
    open(object_ref(obj)) {
        step();
        step();
        step();
        step();
        step();
    }
    execute();
    simp();
}

int32 count_before_retain(struct object* obj) {
    requires count(object_ref(obj)) < 2147483647;
    owns object_ref(obj);
    produces object_ref(obj);
    ensures result == count(object_ref(obj)) - 1;
} by {
    open(object_ref(obj)) {
        step();
        step();
    }
    execute();
    simp();
}
```

```expect
pass
```
