# Alignment is never inferred from the pointee type

A `struct node*` parameter is not evidence that its address is 8-byte
aligned: casts and arithmetic can form misaligned values of that type. Without
a contract clause the claim stays undecided.

```c filename=aligned_requires_evidence.c
struct node {
    int32 value;
    unsigned long word;
};

int32 aligned_requires_evidence(struct node* node) {
    return 0;
}
```

```click
verifying "aligned_requires_evidence.c";

int32 aligned_requires_evidence(struct node* node) {
    ensures aligned(node, 8);
} by {
    execute();
    simp();
}
```

```expect
fail: did not retain a complete proof for `aligned_requires_evidence.ensures_0`
```
