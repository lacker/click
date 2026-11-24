# An open control cannot supply its closed facts again

The helper requires the whole control, but its counter and authority are
exposed in the caller. The caller cannot lend that suspended control.

```c filename=reopen.c
struct object { int32 refs; };
void inspect(struct object* obj) { }
void broken(struct object* obj) { obj->refs = 0; inspect(obj); }
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
void broken(struct object* obj) {
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
