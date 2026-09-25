# An open population cannot supply its closed facts again

```c filename=reopen.c
struct object { int32 refs; };
void inspect(struct object* obj) { }
void broken(struct object* obj) { obj->refs = 0; inspect(obj); }
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
void broken(struct object* obj) {
    owns reference(obj);
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
fail: population invariant at call entry
```
