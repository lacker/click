# One dependent clause set serves every contract form

`probe` and the named contract `DependentPair` declare the clause set of
`mdtests/contract_owns_composite_argument.md`: `owns pair(node)` supplies
the link that `owns pair(node->left->left)` must load to form its argument,
and that one supplies the next. The same clause set carries through each
form the kernel applies a contract in, with no proof step about the
composites in any of them:

- `probe` verifies directly and is certified independently;
- `invoke` applies `DependentPair` through a callback, so the dependent
  clauses are evaluated as a named contract at a call;
- `probe_is_dependent_pair` is the explicit execution theorem that `probe`
  satisfies `DependentPair`, and `theorem_caller` uses it; and
- `automatic_caller` passes `&probe` where `DependentPair` is required with
  no theorem in scope, so the refinement is formed automatically within the
  admitted exact fragment.

```c filename=dependent_pair_forms.c
struct node {
    struct node *left;
    int32 value;
};

void probe(struct node *node) { }

void invoke(void (*callback)(struct node *), struct node *node) { callback(node); }

void theorem_caller(struct node *node) { invoke(&probe, node); }

void automatic_caller(struct node *node) { invoke(&probe, node); }
```

```click
resource pair(node: struct node*) {
    owns node[0..1];
    owns node->left[0..1];
}

verifying "dependent_pair_forms.c";

contract void DependentPair(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    owns pair(node);
    owns pair(node->left->left);
    owns pair(node->left->left->left);
}

void probe(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    owns pair(node);
    owns pair(node->left->left);
    owns pair(node->left->left->left);
}

theorem probe_is_dependent_pair() executes probe(struct node* node) {
    ensures DependentPair(&probe) by {
        execute();
        simp();
    }
}

void invoke(void (*callback)(struct node*), struct node* node) {
    requires DependentPair(callback);
    requires node != 0;
    requires node->left != 0;
    owns pair(node);
    owns pair(node->left->left);
    owns pair(node->left->left->left);
} by {
    execute();
    simp();
}

void theorem_caller(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    owns pair(node);
    owns pair(node->left->left);
    owns pair(node->left->left->left);
} by {
    apply(probe_is_dependent_pair());
    execute();
    simp();
}

void automatic_caller(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    owns pair(node);
    owns pair(node->left->left);
    owns pair(node->left->left->left);
} by {
    execute();
    simp();
}
```

```expect
pass
```
