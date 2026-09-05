# A tagged null word clears back to null

`rb_set_parent_color(node, NULL, RB_BLACK)` forms the integer `1` from a
null pointer. Clearing the tag recovers the canonical null pointer, whether
the null came from the literal `0` or from a parameter known to be null.

```c filename=tagged_pointer_null_word.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* literal_null_round_trip() {
    unsigned long word = (unsigned long)0 + 1;
    return (struct node*)(word & ~3);
}

struct node* known_null_round_trip(struct node* next) {
    unsigned long word = (unsigned long)next + 1;
    return (struct node*)(word & ~3);
}
```

```click
verifying "tagged_pointer_null_word.c";

struct node* literal_null_round_trip() {
    ensures result == 0;
} by {
    execute();
    simp();
}

struct node* known_null_round_trip(struct node* next) {
    requires next == 0;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
