# pointer-valued volatile objects retain provenance across sequential updates

The volatile qualifier can belong to a pointer object or to a pointer-valued
cell reached through another pointer. These accesses remain sequential facts;
they do not grant access to the struct pointee.

```c filename=c_volatile_pointer_objects.c
struct node {
    int32 value;
    struct node *left;
};

struct node *update_pointer_cell(struct node *parent, struct node *replacement) {
    struct node * volatile *cell = (struct node * volatile *)&parent->left;
    *cell = replacement;
    return *cell;
}
```

```click
verifying "c_volatile_pointer_objects.c";

struct node *update_pointer_cell(struct node *parent, struct node *replacement) {
    requires loadable(parent->left);
    consumes parent->left;
    mutable parent->left;
    ensures result == replacement;
    produces parent->left;
}
```

```expect
pass
```
