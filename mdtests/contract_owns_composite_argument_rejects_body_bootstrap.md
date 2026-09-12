# A composite body cannot bootstrap its own dependent argument

The body of `cell` owns a range at its parameter, but owning
`cell(node->left)` must not make the load of `node->left` available while
forming that argument.  There is no view or loadability precondition for the
pointer field here.

```c filename=body_bootstrap.c
struct node {
    struct node *left;
};

void probe(struct node *node) { }
```

```click
resource cell(node: struct node*) {
    owns node[0..1];
}

verifying "body_bootstrap.c";

contract void Bootstrap(struct node* node) {
    requires node != 0;
    owns cell(node->left);
}
```

```expect
fail: could not evaluate the contract entry resources: FunctionContract("could not evaluate resource `cell` argument 0
```
