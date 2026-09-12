# A conjunctive requirement preserves nested dynamic loadability

Loadability may be one conjunct of a larger requirement.  The checked read
authority from that atom is still available when a dependent composite
argument reads its pointer field, while the arithmetic conjunct remains part
of the contract proposition.

```c filename=nested_dynamic_dependent_pair.c
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

verifying "nested_dynamic_dependent_pair.c";

contract void NestedDynamicDependentPair(struct node* node, int32 n) {
    requires node != 0;
    requires n >= 1 and loadable(node[0..n]);
    requires n <= 2147483647;
    owns cell(node->left);
}
```

```expect
pass
```
