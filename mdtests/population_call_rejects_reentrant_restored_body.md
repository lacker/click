# Restoring a value cannot lend a still-open control

The helper requires the closed control. Restoring the counter value inside
the open scope does not independently restore the control for a nested call.

```c filename=reopen.c
struct object { int32 refs; };
void inspect(struct object* obj) { }
void restored(struct object* obj) { obj->refs = obj->refs; inspect(obj); }
```

```click
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(reference(obj));
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}
verifying "reopen.c";
void inspect(struct object* obj) {
    owns control(obj);
}
void restored(struct object* obj) {
    owns control(obj);
} by {
    with(control(obj)) {
        step();
        step();
    }
    close();
}
```

```expect
fail: population body is open
```
