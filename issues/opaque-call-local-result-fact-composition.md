# Compose pure facts through opaque-call local results

## Problem

Verified opaque calls apply their contracts correctly, but grouped `simp()`
cannot always produce a replayable surface certificate for a transitive fact
that passes through a C local holding an earlier call's result.

The binary-tree leaf pipeline exposes the gap naturally:

```c
left = tree_empty();
right = tree_empty();
made = tree_make_root(node, value, left, right);
swapped = tree_swap_children(node);
```

`tree_empty` ensures its result is null, `tree_make_root` ensures the child
fields equal its arguments, and `tree_swap_children` ensures those fields are
exchanged. Nevertheless, adding either of these valid pipeline postconditions
currently fails certificate replay:

```click
ensures node->left == 0;
ensures node->right == 0;
```

The diagnostic's surface premises retain the later field equalities but omit
the useful equality between each statement-local pointer and the null result
of `tree_empty`. This resembles the deliberate hiding of statement-local
opaque-call facts, but here it prevents composition of public callee
postconditions.

## Desired behavior

Public facts established by a verified call should remain usable through the
local receiving its result when later public call postconditions refer to that
local. Expansion and independent replay must agree on the resulting finite
fact chain; internal memory identities and other implementation-only call
facts should remain hidden.

## Acceptance criteria

- Restore the two null child postconditions in
  `examples/binary-tree/tree_leaf_pipeline`.
- `simp()` or its explicit expansion proves both postconditions using only
  replayable Surface Click facts.
- Existing tests that hide genuinely internal statement-local opaque-call
  facts remain green.
- Add a focused regression test that distinguishes a public result equality
  needed by a later call from internal call-execution details.
