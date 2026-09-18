# A branch-on-count release consumes one of an unknown population

The ordinary refcount release gives up one reference, and frees the child only
when it held the last one. The caller may hold any number of references, so the
callee's contract must be able to say "consume one of an arbitrary population".
Today the transferred quantity is a fixed constant, so the non-final path is
mistaken for the end of the population and its allocation is demanded.

```c filename=child_release_branch_on_count.c
struct child {
    int32 refs;
};

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}
```

```click
resource child_ref(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    fact obj->refs == count(child_ref(obj));
}

verifying "child_release_branch_on_count.c";

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_ref(obj);
} by {
    if obj->refs == 1 {
        unfold(child_ref(obj));
        execute();
        simp();
    } else {
        open(child_ref(obj)) {
            execute();
        }
        simp();
    }
}
```

```expect
fail: count(child_ref(...)) != 0
```
