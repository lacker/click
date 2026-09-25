# A call that changes a population drops the caller's cached body cell

At a call's return the kernel certifies the population's body fact at the
post-call state, `obj->refs == count(object_ref(obj))` with the post-call
count. That fact is true only because the call havoc drops what the caller
had cached for `obj->refs`: the callee's footprint is derived from the
population body, which owns the cell, and the caller keeps owning no member
that holds it (a population unit is counted, not a residual resource, so the
kept-by-caller rule has nothing to open). Were the cached value kept -- or
named across the call at its pre-call value -- the certified fact would say
`before == count + 1` beside the closed body's `before == count`, and that
contradiction would prove anything, the false `ensures` below included
(`caller` returns the pre-call count, which is positive, never `12345`).

This pins that protective behaviour. The same program with the true
`ensures result == count(object_ref(obj)) - 1` verifies
(`population_call_keeps_what_it_may_and_drops_the_body_cell.md`).

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
resource object_ref(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "population_call_cached_body.c";

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

int32 caller(struct object* obj) {
    requires count(object_ref(obj)) < 2147483647;
    owns object_ref(obj);
    produces object_ref(obj);
    ensures result == 12345;
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
fail: `ensures result == 12345` failed
```
