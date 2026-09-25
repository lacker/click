# A call inside an open population does not assume that population's body

A call's return re-establishes the body facts of every active counted
population as certified facts at the post-call state. The callee proved those
facts only for populations it could see: a call is refused a unit whose body
is open (`population_call_requires_closed_body.md`), so a population the
caller holds open is one the callee never touched. Its body fact is the
caller's to restore when it closes the body, and the caller's open memory may
contradict it.

The return used to assume it anyway. Below, `broken` opens `object_ref(obj)`,
stores `0` into the count cell while holding one reference, and calls an
unrelated `three()`; the return certified `obj->refs == count(object_ref(obj))`
at a state where `obj->refs` is `0` and the count is positive, and that
contradiction closed the body and proved the false `ensures result == 1`
(`broken` returns `0`), and `click audit` accepted it. A population the caller
holds open is now skipped, so the close has to prove the body fact from what
the caller knows, and it cannot.

```c filename=call_inside_open_population.c
struct object {
    int32 refs;
};

int32 three() {
    return 3;
}

int32 broken(struct object* obj) {
    obj->refs = 0;
    three();
    return 0;
}
```

```click
resource object_ref(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "call_inside_open_population.c";

int32 three() {
    ensures result == 3;
} by auto;

int32 broken(struct object* obj) {
    owns object_ref(obj);
    ensures result == 1;
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
fail: requires an exact body fact
```
