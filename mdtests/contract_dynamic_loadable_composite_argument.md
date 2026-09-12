# A dynamic loadability requirement authorizes a dependent composite argument

The resource argument reads a pointer field.  Its caller supplies a symbolic
length loadability requirement, so the kernel may use the checked read view
without inventing a constant memory cell.

```c filename=dynamic_dependent_pair.c
struct node {
    struct node *left;
    int32 value;
};

void probe(struct node *node, int32 n) { }
```

```click
resource cell(node: struct node*) {
    owns node[0..1];
}

verifying "dynamic_dependent_pair.c";

contract void DynamicDependentPair(struct node* node, int32 n) {
    requires node != 0;
    requires n >= 1;
    requires n <= 2147483647;
    requires loadable(node[0..n]);
    owns cell(node->left);
}
```

```expect
pass
```
