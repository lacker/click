# Recursive Zero List

This project combines recursive C contracts with a guarded recursive composite
resource. A nonnull `zero_list(node)` owns the node fields, records that its
value is zero, and contains the still-folded resource for `node->next`.

`zero_list_empty` and `zero_list_push` build lists from caller-supplied nodes.
`zero_list_sum` accepts a nonempty list, views one resource layer at a time, and
calls its own verified contract opaquely on a nonempty tail. Its ordinary
contract proves that every returning execution yields zero. Its separate
`decreases resource zero_list(node)` declaration proves termination because
the recursive call receives the direct contained tail witness.

`zero_list_sum_bounded` also takes numeric fuel and declares `decreases fuel`.
Its recursive edge passes `fuel - 1` under a positive-fuel guard, so Click can
construct separate termination evidence with the current numeric checker.
`zero_list_pipeline` directly initializes a two-node list, folds it, composes
both traversal contracts, and returns the list resource.

The structural check is deliberately narrower than general resource
provenance: it supports direct immutable recursion, requires the active resource
guard as a function precondition, and rechecks the exact direct child through C
local aliases. Pointer inequality or a same-named unrelated resource is not a
termination argument.
