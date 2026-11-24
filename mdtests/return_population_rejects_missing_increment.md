# Producing a reference does not prove its stored count invariant

An explicit member birth changes the population while the unchanged C returns
without incrementing its counter. Closing the separate authority-bearing
control must restore the counter/count equation and therefore fails.

```c filename=retain.c
struct object { int32 refs; };
struct object* retain(struct object* obj) { return obj; }
```

```click
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(reference(obj));
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}
verifying "retain.c";
struct object* retain(struct object* obj) {
    requires count(reference(obj)) < 2147483647;
    owns control(obj);
    owns reference(obj);
    produces reference(obj);
    ensures result == obj;
} by {
    with(control(obj)) { fold(reference(obj)); }
    close();
}
```

```expect
fail: Requires to_integer(obj->refs) == to_integer(count(reference(obj)))
```
