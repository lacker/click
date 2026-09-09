# Closing one population must not assume another population's new invariant

```c filename=retain.c
struct object { int32 refs; };
void retain(struct object* left, struct object* right) { left->refs += 1; }
```

```click
resource reference(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}
verifying "retain.c";
void retain(struct object* left, struct object* right) {
    requires left != right;
    requires count(reference(left)) < 2147483647;
    requires count(reference(right)) < 2147483647;
    owns reference(left);
    owns reference(right);
    produces reference(left);
    produces reference(right);
} by {
    open(reference(right)) {
        open(reference(left)) { execute(); }
    }
    simp();
}
```

```expect
fail: requires an exact body fact
```
