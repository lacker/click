# Producing a reference does not prove its stored count invariant

```c filename=retain.c
struct object { int32 refs; };
struct object* retain(struct object* obj) { return obj; }
```

```click
resource reference(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}
verifying "retain.c";
struct object* retain(struct object* obj) {
    requires count(reference(obj)) < 2147483647;
    owns reference(obj);
    produces reference(obj);
    ensures result == obj;
} by {
    open(reference(obj)) { execute(); }
    simp();
}
```

```expect
fail: requires an exact body fact
```
