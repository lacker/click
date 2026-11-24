# A helper that consumes a member must spend it

A helper that borrows the control and declares `consumes reference(obj)` but
never spends the member must be refused. Its caller would otherwise apply a
death that never happened, and the caller's control equation would state that
the counter is zero while the C counter is still one. The C is unchanged; the
false postcondition `result == 0` must not verify.

```c filename=authority_helper_consume_without_spend_rejected.c
struct object { int refs; };
void drop(struct object *obj) {}
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 1;
    drop(obj);
    int left = obj->refs;
    free(obj);
    return left;
}
```

```click
verifying "authority_helper_consume_without_spend_rejected.c";
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == count(reference(obj));
}
void drop(struct object* obj) {
    owns control(obj);
    consumes reference(obj);
}
int32 run() {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch { true => { step(); close(); } false => {} }
    step();
    fold(authority(reference(obj)));
    fold(reference(obj));
    fold(control(obj));
    step();
    unfold(control(obj));
    unfold(authority(reference(obj)));
}
```

```expect
fail: Requires consumes reference(obj)
```
