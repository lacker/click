# Qualified pointer casts preserve const views

A cast may add pointee `const`, and an explicit cast back to an unqualified
pointer does not erase a const view already carried by the source pointer.
The pointer identity and the struct field layout remain available through both
forms.

```c filename=const_pointer_cast.c
struct node {
    int32 value;
    struct node *next;
};

const struct node *as_const(struct node *node) {
    return (const struct node *)node;
}

const struct node *round_trip(const struct node *node) {
    return (struct node *)node;
}

int32 read_value(struct node *node) {
    return ((const struct node *)node)->value;
}
```

```click
verifying "const_pointer_cast.c";

const struct node *as_const(struct node *node) {
    requires node != 0;
    ensures result == node;
} by { execute(); simp(); }

const struct node *round_trip(const struct node *node) {
    requires node != 0;
    ensures result == node;
} by { execute(); simp(); }

int32 read_value(struct node *node) {
    requires node != 0;
    views node->value;
    ensures result == node->value;
} by { execute(); simp(); }
```

```expect
pass
```
