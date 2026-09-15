# A dependent composite argument crosses a call boundary

`probe`'s clause set is the one `mdtests/contract_owns_composite_argument.md`
verifies at `probe`'s own entry: `owns pair(node)` supplies the link that
`owns pair(node->left->left)` must load to form its argument. `call_probe`
declares the same clauses and calls `probe`, and the call verifies with no
proof step about the composites: the callee's precondition
`node->left != 0` reads a cell the transferred clause set holds, so the
call discharges that read from the clause set opened by its definitions,
exactly as `probe`'s entry does; and the borrowed `owns pair(node->left->left)`
is returned as the resource selected at entry, its address read the same
way. Nothing is owned twice: the opened cells are read authority for the
judgment and the transfer keeps the folded heads.

```c filename=dependent_pair_call.c
struct node {
    struct node *left;
    int32 value;
};

void probe(struct node *node) { }

void call_probe(struct node *node) { probe(node); }
```

```click
resource pair(node: struct node*) {
    owns node[0..1];
    owns node->left[0..1];
}

verifying "dependent_pair_call.c";

void probe(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    owns pair(node);
    owns pair(node->left->left);
}

void call_probe(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    owns pair(node);
    owns pair(node->left->left);
} by {
    execute();
    simp();
}
```

```expect
pass
```
