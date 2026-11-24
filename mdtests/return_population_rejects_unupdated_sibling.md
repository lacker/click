# Closing one population must not assume another population's new invariant

Both populations have separate ordinary counter/authority controls. The proof
explicitly creates a member in each, but the unchanged C increments only the
left counter. Restoring the left control cannot assume the right invariant.

```c filename=retain.c
struct object { int32 refs; };
void retain(struct object* left, struct object* right) { left->refs += 1; }
```

```click
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(reference(obj));
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}
verifying "retain.c";
void retain(struct object* left, struct object* right) {
    requires left != right;
    requires count(reference(left)) < 2147483647;
    requires count(reference(right)) < 2147483647;
    owns control(left);
    owns reference(left);
    owns control(right);
    owns reference(right);
    produces reference(left);
    produces reference(right);
} by {
    with(control(right)) {
        with(control(left)) {
            step();
            fold(reference(left));
            fold(reference(right));
        }
    }
    close();
}
```

```expect
fail: Requires to_integer(right->refs) == to_integer(count(reference(right)))
```
