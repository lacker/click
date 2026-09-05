# An address compared with an arbitrary integer is undecided

An address word may coincide with any integer value, so comparing it with an
integer that has no pointer origin proves nothing in either direction. The
postcondition claiming the comparison is false cannot be established.

```c filename=pointer_address_unrelated_integer_undecided.c
struct node {
    int32 value;
    unsigned long word;
};

int32 compare_with_integer(struct node* node, unsigned long word) {
    return word == (unsigned long)node;
}
```

```click
verifying "pointer_address_unrelated_integer_undecided.c";

int32 compare_with_integer(struct node* node, unsigned long word) {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: did not retain a complete proof for `compare_with_integer.ensures_0`
```
