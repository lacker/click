# Heap-derived addition bounds do not efficiently prove overflow freedom

## Summary

Click can verify `x + 1` from a suitable bound, but it does not efficiently
use ordinary interval facts to prove that a general symbolic addition is
overflow-free. The problem is especially visible when the operands are loads
from composite resources, because equivalent loads can carry different memory
snapshot spellings.

## Reproduction

In `examples/binary-tree`, give the root and both non-null children values in
the range `0..715827882`, then verify:

```c
return node->value + node->left->value + node->right->value;
```

The three upper bounds mathematically keep the result below `INT32_MAX`, but a
smart `step()` spends a long time searching. A simple `step() using { ... }`
with the six lower and upper bounds still reports possible signed overflow.

## Desired behavior

The overflow reasoner should derive a conservative signed interval for each
operand, including nested additions, and decide that addition cannot overflow
when the summed lower and upper endpoints remain within the `int32` range.
Matching heap-derived terms must use the existing sound memory-snapshot
equivalence machinery without triggering deep, repeated canonicalization.

Add focused kernel tests for positive, negative, nested-addition, and
cross-snapshot cases, then add the one-level sum source to the binary-tree
sidecar's `verifying` list with general bounded values.
