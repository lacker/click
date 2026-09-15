# Frontier: a dependent composite argument at a call boundary

`probe`'s clause set is the one `mdtests/contract_owns_composite_argument.md`
verifies at `probe`'s own entry and prepares as a named contract:
`owns pair(node)` supplies the link that `owns pair(node->left->left)` must
load to form its argument. `call_probe` declares the same clauses and calls
`probe`. The call is refused today: the dependent argument lowers to the
loadability of `node->left` as a precondition of `probe`, and the caller,
holding `pair(node)` folded, cannot discharge it by the retained-evidence
rule a call precondition is held to, with or without observing the
composite. At `probe`'s own entry the whole clause set supplies that load.

This is a known gap recorded in `issues/memory-vs-resources.md` (R2 call
forms), pinned here as a frontier so the gate holds the reproduction. The
named-callback application, the execution theorem, and automatic formation
through a call fail on the same precondition. When the call boundary
evaluates a dependent clause set the way the entry does, this expectation
flips to `pass` and the fixture becomes the R2 call-form regression.

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
fail: `call_probe.contract` tactic 0: `step()` is missing prerequisite (probe precondition): loadable(base=arg-memory@v100000 * 4, bytes=8)
```
