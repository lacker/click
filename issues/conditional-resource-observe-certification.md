# Observing nested conditional resources does not replay in certification

## Summary

After unfolding an owned conditional recursive resource, `observe` can expose
the fields of a non-empty child and surface execution can use those views.
Kernel certification may nevertheless report a missing child-field view and
reject the replayed execution path.

## Reproduction

In the binary-tree example, start with `owns tree(node)`, require `node` and a
child to be non-null, then use:

```click
unfold(tree(node));
observe(tree(node->left));
step() using { ... }
```

Surface replay reaches the return, while certification can report that the
view of `node->left->value` is missing. One-level observation is not affected:
the binary-tree leaf predicate successfully observes the root tree and reads
its two links.

## Desired behavior

The observation law for an active conditional composite body should produce a
replayable derivation for every projected core resource. Surface execution and
kernel certification must agree on both the memory snapshot spelling and the
resulting resource representation. Add a focused nested-conditional-resource
test, then prefer `observe` over destructive unfold/fold in the binary-tree
read-only algorithms.
