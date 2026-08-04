# Nested composite rotation certification

## Summary

The natural proof of a left rotation over the guarded `tree` resource passes
substantial parts of surface checking but cannot currently be replayed by the
kernel. The small reproducer is
`examples/binary-tree/tree_rotate_left.c`.

The intended contract consumes `tree(node)`, requires `node->right != 0`,
allows writes to `node->right` and `node->right->left`, and produces a tree at
the returned root. Its intended proof is simply:

```click
unfold(tree(node));
unfold(tree(node->right));
execute();
fold(tree(node));
fold(tree(result));
frame();
simp();
```

## Current failures

Three related seams show up:

1. `mutable node->right->left` is lowered as a range rooted at the old value of
   `node->right`, but without the final `left` field offset. The executed store
   is therefore reported outside the mutable footprint.
2. Widening the mutable range lets surface checking continue, but kernel replay
   then lacks the nested field resource produced by unfolding the pivot tree.
3. Supplying the pivot as a stable parameter and spelling out both nodes' field
   resources gets still farther, but rebuilding the two tree resources ends in
   a surface/kernel ghost-representation mismatch.

These are not good reasons to distort the example API or weaken its contract.

## Desired behavior

Nested member paths in effects should retain every field offset and be fixed at
function entry. Unfolding a conditional owned child resource should produce the
same certifiable field resources in surface execution and kernel replay.
Re-folding the old root and new root after the two pointer stores should leave
equivalent ghost representations.

Once those properties hold, add `tree_rotate_left.c` to the binary-tree
sidecar's `verifying` list with the direct contract and proof above.
