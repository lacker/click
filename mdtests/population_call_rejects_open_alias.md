# Restoring a value cannot duplicate suspended control custody

The aliased helper argument denotes the same open control. A self-assignment
restores its value but cannot lend the control while its body remains exposed.

```c filename=reopen.c
struct object { int32 refs; };
void inspect(struct object* obj) { }
void restored(struct object* obj, struct object* alias) { obj->refs = obj->refs; inspect(alias); }
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
void restored(struct object* obj, struct object* alias) {
    owns control(obj);
    requires alias == obj;
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
