# symbolic quantities reject recursive composite resources

Recursive resource bodies describe one structurally smaller child per owned
instance. Symbolic coefficients use one population-wide body, so applying a
coefficient to a recursive composite is rejected until Click has a certified
semantics for that combination.

```c filename=symbolic_quantity_recursive_composite.c
struct node {
    struct node* next;
};

void hold_many(struct node* node, int32 amount) {
}
```

```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->next;
        contains list(node->next);
    }
}

verifying "symbolic_quantity_recursive_composite.c";

void hold_many(struct node* node, int32 amount) {
    requires 0 <= amount;
    owns amount of list(node);
} by auto;
```

```expect
fail: symbolic quantities for recursive composite resource `list` are not supported
```
