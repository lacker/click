# A pointer comparison neither rule settles

Knowing one pointer is null says nothing about a pointer whose null-ness the
context never settled: `q` may well be null too, and then the test is true.
Owning one object says nothing about a pointer no other ownership separates
from its base. In both shapes the comparison stays undecided, execution keeps
both paths, and the postcondition fails on the path that returns `1`.

Neither rule ever decides a comparison true. Two pointers may be equal for
reasons no fact in the context records, so a missing disequality is a missing
decision and not a proof of equality.

```c filename=pointer_disequality_rejects_undecided.c
struct node {
    struct node *left;
    int32 value;
};

int32 only_one_side_is_null(struct node *p, struct node *q) {
    if (p == q)
        return 1;
    return 0;
}

int32 only_one_object_is_owned(struct node *a, struct node *b) {
    if (a == b)
        return 1;
    return 0;
}
```

```click
verifying "pointer_disequality_rejects_undecided.c";

int32 only_one_side_is_null(struct node* p, struct node* q) {
    requires p == 0;
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 only_one_object_is_owned(struct node* a, struct node* b) {
    owns a->left;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal: result == 0
```
