# Add a recursive zero-list traversal example

## Purpose

The recursion features now have focused mdtests, but no larger project combines
recursive C contracts, recursive composite resources, opaque self-calls, and
optional termination. Add one deliberately small example before extending the
language again. Its job is to reveal ordinary composition problems while the
proof is still easy to inspect.

Use `examples/recursive-zero-list/`. A separate project keeps the existing
`linked-list` example focused on ownership transfer and lets this example give
every node a strong logical value invariant.

## Proposed model

Define a guarded recursive resource whose nonnull nodes contain zero:

```click
resource zero_list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        fact node->value == 0;
        contains zero_list(node->next);
    }
}
```

The exact surface definition must pass the existing stability rule: a fact that
loads `node->value` is justified by contained ownership of that field. The
example should include simple construction code over caller-supplied nodes so
the resource is not merely an unexplained contract precondition.

Verify two read-only recursive traversals:

1. `zero_list_sum(node)` returns zero after recursively traversing the tail.
   It views `zero_list(node)`, is immutable, and has `ensures result == 0`.
   It has no `decreases` clause. The proof is partial correctness even though
   the inductive resource gives a human a structural termination argument.
2. `zero_list_sum_bounded(node, fuel)` stops at null or nonpositive fuel and
   otherwise recurses with `fuel - 1`. It has the same result guarantee and a
   numeric `decreases fuel` clause, so the existing termination checker should
   certify it independently of the future structural rule.

Returning zero is intentionally not a toy postcondition. It forces the proof
to use the per-node resource fact, the recursive call's public result, and the
definedness of `0 + 0`, while avoiding an unrelated integer-overflow bound on a
general list sum.

## Proof expectations

- Null and nonnull paths are explicit enough that the proof shows where the
  conditional resource body becomes available.
- A nonnull path observes or unfolds exactly one resource layer, calls the
  recursive contract on the contained tail, and restores or preserves the
  caller-visible resource as required.
- Recursive calls remain opaque. The verifier must not inline C bodies to a
  depth budget.
- Public call-result facts compose through the receiving C local without
  exposing call-havoc names or symbolic kernel identities.
- The unbounded and fuel-bounded functions use the same partial contract rule;
  only the latter receives separate termination evidence.
- Proof scripts remain short enough to teach from. A generated certificate may
  be detailed, but the checked source should not become a dump of unrelated
  ambient facts.

## What to do with discoveries

This issue does not authorize a new resource calculus. Fix a small diagnostic,
surface spelling, fold/observe, call-result, or framing wart in the same chunk
when the intended rule is already clear. Record a distinct issue before making
any change to trusted semantics or adding new syntax. Structural termination
and pure induction stay in their own issues even if the example motivates
them.

## Verification and documentation

- Register the project through the ordinary examples-directory test; do not
  quarantine it.
- Profile the project. No simple tactic may cross the simple-tactic budget.
  Expand any genuinely slow successful smart tactic and keep the readable
  source certificate.
- Add a README explaining partial correctness, numeric termination, and the
  structural claim Click still does not make.
- Link the project from `docs/examples.md` and the larger-examples guide.
- If expansion is needed, verify the expanded artifact and check that
  re-expansion is stable through the normal audit workflow.

## Acceptance criteria

- The project constructs and traverses a nontrivial recursive zero-list.
- The unbounded traversal verifies without claiming termination.
- The bounded traversal receives kernel-checked numeric termination evidence.
- The recursive contract uses a contained tail resource rather than an
  artificial flattened buffer model.
- The full examples test remains fast and unquarantined.
- Documentation says exactly what is and is not proved.

## Non-goals

- General list sums or arithmetic overflow policy.
- Allocation, deallocation, or C library modeling.
- Structural termination evidence.
- General theorem induction.
- Automatically unfolding arbitrary recursive resources.
