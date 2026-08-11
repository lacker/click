# Binary-tree grouped simp transition has no expressible certificate

`examples/binary-tree` fails ordinary verification:

```text
`tree_is_leaf.contract` path 0, tactic 3: grouped `simp` could not certify its
complete claim transition
claim 5 (`tree_is_leaf.ensures_4`): expressible path facts do not replay the
postcondition derivation: ConditionIs(Constant(false), true)
```

The failure began at commit `e9460ff` ("Reject opaque outcome certificates"),
which removed the fallback that let a post-execution simplification emit the
smart tactic itself as its own certificate. That rejection is correct: a smart
success must lower to an explicit simple certificate, and the opaque fallback
hid exactly this gap. The bug is that the grouped transition's postcondition
derivation selects evidence that the expressible path facts cannot replay —
the derivation appears to route through a negated constant condition rather
than the leaf-case implications that actually close the claim.

The violated invariant: every grouped `simp` claim transition must lower to a
replayable explicit certificate built from expressible path facts.

## Reproduction

```sh
target/debug/click verify examples/binary-tree
```

The project is quarantined in `tests/examples.rs` until this is fixed. A
reduced regression should isolate one boolean-result leaf test (result
implications plus null-field facts) whose grouped transition exercises the
same derivation shape without the rest of the tree project.

## Acceptance criteria

- The unchanged binary-tree project verifies and leaves quarantine.
- A focused mdtest regression covers the reduced transition shape.
- The fix adds expressible certificate steps or repairs derivation selection;
  it does not restore the opaque-certificate fallback removed by `e9460ff`.
