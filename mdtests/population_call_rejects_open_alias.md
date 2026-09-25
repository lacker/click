# Restoring a value does not restore suspended access authority

```c filename=reopen.c
struct object { int32 refs; };
void inspect(struct object* obj) { }
void restored(struct object* obj, struct object* alias) { obj->refs = obj->refs; inspect(alias); }
```

```click
resource reference(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}
verifying "reopen.c";
void inspect(struct object* obj) {
    owns reference(obj);
} by { execute(); simp(); }
void restored(struct object* obj, struct object* alias) {
    owns reference(obj);
    requires alias == obj;
} by {
    open(reference(obj)) {
        step();
        step();
        execute();
    }
    simp();
}
```

```expect
fail: population body is open
```
