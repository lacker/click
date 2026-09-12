# A dynamic composite argument still needs a loadability requirement

The bound on the symbolic length does not itself authorize reading the
pointer field used to form the composite argument.  Without `loadable`, the
entry evaluator must reject the clause even though its body is a memory
resource.

```c filename=dynamic_dependent_pair_missing.c
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

verifying "dynamic_dependent_pair_missing.c";

contract void DynamicDependentPair(struct node* node, int32 n) {
    requires node != 0;
    requires n >= 1;
    requires n <= 2147483647;
    owns cell(node->left);
}
```

```expect
fail: could not evaluate the contract entry resources: FunctionContract("could not evaluate resource `cell` argument 0
```
