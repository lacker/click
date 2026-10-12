# Alignment does not justify stepping beyond one viewed record

The unchanged contract views one struct record but permits indices two and
three. Those steps leave the pointed-to object. A mathematical alignment
identity cannot establish that C pointer formation is defined, so verification
refuses the original claim. The kernel's symbolic alignment certificate remains
covered independently of this invalid C precondition.

```c filename=aligned_symbolic_displacement.c
struct pair {
    int32 a;
    int64 b;
};

int32 element_is_aligned(struct pair *p, int32 i) {
    return ((unsigned long)(p + i) & 7) == 0;
}
```

```click
verifying "aligned_symbolic_displacement.c";

int32 element_is_aligned(struct pair* p, int32 i) {
    requires aligned(p, 8);
    requires 0 <= i and i < 4;
    views *p;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
