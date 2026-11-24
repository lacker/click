# Consuming one reference does not justify clearing a nonfinal stored count

One checked consumption leaves at least two members because the entry count
is greater than two. The unchanged C clears the counter to zero, so its
ordinary authority-bearing control cannot restore the remaining-count equation.

```c filename=release.c
struct object { int32 refs; };
void release(struct object* obj) { obj->refs = 0; }
```

```click
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(reference(obj));
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}
verifying "release.c";
void release(struct object* obj) {
    requires 2 < count(reference(obj));
    owns control(obj);
    owns reference(obj);
    consumes reference(obj);
} by {
    with(control(obj)) { unfold(reference(obj)); }
    close();
}
```

```expect
fail: Requires to_integer(obj->refs) == to_integer(count(reference(obj)))
```
