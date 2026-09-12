# a `have` that reads a local before its assignment names the local

A local declared but not yet assigned has no value at the frontier, so reading
it has no defined path and the kernel lowering produces none. Reporting the
path count sends the reader looking for a lowering defect; the actionable fact
is that the proof stands before the statement that gives the local its value.

```c filename=have_names_a_local_before_its_assignment.c
struct cell {
    int32 value;
    struct cell* next;
};

int32 alias_read(struct cell *root) {
    struct cell *p;

    p = root;
    return p->value;
}
```

```click
verifying "have_names_a_local_before_its_assignment.c";

int32 alias_read(struct cell* root) {
    owns root->value;
    requires root != 0;
    ensures result == old(root->value);
} by {
    step();
    have p->value == root->value by { simp(); }
    step();
    step();
    simp();
}
```

```expect
fail: local `p` has no value at this frontier
```
