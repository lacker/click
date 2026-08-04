# Recursive Zero List

This project combines recursive C contracts with a guarded recursive composite
resource. A nonnull `zero_list(node)` owns the node fields, records that its
value is zero, and contains the still-folded resource for `node->next`.

`zero_list_empty` and `zero_list_push` build lists from caller-supplied nodes.
`zero_list_sum` accepts a nonempty list, views one resource layer at a time, and
calls its own verified contract opaquely on a nonempty tail. It proves that
every returning execution yields zero. That is a partial-correctness statement:
the contract alone does not say the C call returns.

`zero_list_sum_bounded` also takes numeric fuel and declares `decreases fuel`.
Its recursive edge passes `fuel - 1` under a positive-fuel guard, so Click can
construct separate termination evidence with the current numeric checker.
`zero_list_pipeline` directly initializes a two-node list, folds it, composes
both traversal contracts, and returns the list resource.

The inductive list resource gives a human a structural termination argument for
the unbounded traversal, but Click does not yet certify that argument. That
requires a kernel-checked connection between a parent resource witness and the
contained child used by the recursive call; pointer syntax alone is not enough.
