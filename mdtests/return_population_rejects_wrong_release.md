# Consuming one reference does not justify clearing a nonfinal stored count

```c filename=release.c
struct object { int32 refs; };
void release(struct object* obj) { obj->refs = 0; }
```

```click
resource reference(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}
verifying "release.c";
void release(struct object* obj) {
    requires 2 < count(reference(obj));
    owns reference(obj);
    consumes reference(obj);
} by {
    open(reference(obj)) { execute(); }
    simp();
}
```

```expect
fail: requires an exact body fact
```
