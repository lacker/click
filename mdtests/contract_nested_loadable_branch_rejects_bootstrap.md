# A conditional loadability atom is not entry read authority

Loadability under an `or` branch is conditional.  It must not bootstrap the
pointer-field load used to form a dependent composite argument, and the
composite body must not supply that read either.

```c filename=nested_loadable_branch.c
struct node {
    struct node *left;
};

void probe(struct node *node, int32 n) { }
```

```click
resource cell(node: struct node*) {
    owns node[0..1];
}

verifying "nested_loadable_branch.c";

contract void NestedLoadableBranch(struct node* node, int32 n) {
    requires node != 0;
    requires n >= 1 and (n == n or loadable(node[0..n]));
    owns cell(node->left);
}
```

```expect
fail: could not evaluate the contract entry resources: FunctionContract("could not evaluate resource `cell` argument 0
```
