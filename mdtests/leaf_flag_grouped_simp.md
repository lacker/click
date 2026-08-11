# grouped `simp` certifies a boolean leaf check's vacuous implications

A boolean-result leaf test returns early when a pointer field is non-null.
On those paths an ensure such as `left == 0 implies (right == 0 implies
result == 1)` is vacuously true: its lowered consequent is a false constant
and the claim closes only through the contradiction between the assumed
antecedent and the recorded branch fact. The grouped `simp` transition must
express that derivation with explicit path facts rather than an opaque
certificate.

```c filename=leaf_flag.c
struct pair {
    struct pair* left;
    struct pair* right;
};

int32 leaf_flag(struct pair* p) {
    if (p->left != 0) {
        return 0;
    }
    if (p->right != 0) {
        return 0;
    }
    return 1;
}
```

```click
verifying "leaf_flag.c";

int32 leaf_flag(struct pair* p) {
    requires p != 0;
    owns p->left;
    owns p->right;
    immutable;

    ensures result == 1 implies p->left == 0;
    ensures result == 1 implies p->right == 0;
    ensures p->left != 0 implies result == 0;
    ensures p->left == 0 implies (p->right == 0 implies result == 1);
    ensures result == 0 or result == 1;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
