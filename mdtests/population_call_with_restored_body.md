# A restored population body may cross a call boundary

```c filename=reopen.c
struct object { int32 refs; };
void inspect(struct object* obj) { }
void restored(struct object* obj) { obj->refs = obj->refs; inspect(obj); }
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
void restored(struct object* obj) {
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
pass
```
