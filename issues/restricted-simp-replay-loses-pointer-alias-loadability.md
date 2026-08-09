# Restricted simp replay loses pointer-alias loadability

Migrating the first `derive using` in
`examples/owned-segmented-buffer/owned_segmented_buffer.click` to
`simp() using` exposes a certificate-replay failure. The goal is the ordinary
equality

```click
at(statement(4).entry, first_data[0])
    == at(statement(4).entry, first_value)
```

and the two listed premises say that `owner->first_data[0]` has the value and
that `owner->first_data == first_data` at the same program point. Smart
simplification verifies the proof by substituting the pointer equality.
Certificate lowering can select the corresponding `rewrite` and `assumption`
steps, but dependency replay fails before applying them because it cannot
establish the loadability of `first_data[0]`. The context already contains the
loadable backing array, its positive length, and the pointer alias.

This is not smart-search incompleteness: search found a proof, and the selected
rule is an explicit equality rewrite. It is a disagreement between successful
search and simple surface replay. Do not retain `derive using`, add a redundant
element-loadability fact to the example, or reshape the example around the
failure.

A first reduction exposed and fixed one independent surface gap: `rewrite`
now substitutes pointer-offset equalities when the pointer occurs as a memory
load address. A current-state mdtest expands that case to
`rewrite(alias == original); assumption();` and replays. The original
statement-entry case still fails while lowering the expanded proof because its
snapshot spelling cannot recover the element loadability from the certified
array range. Keep the issue open for that snapshot transport failure.
The final `right->data[right->pos] == data[0]` derivation in
`examples/input-cursor` reproduces the same missing `data[0]` loadability when
migrated, so the gap is not specific to owned-segmented-buffer.

## Regression

Add a small mdtest with a loadable array reached through an explicitly known
pointer equality. A `have` whose goal loads one element through the alias and
whose `simp() using` block lists the alias and value equalities must:

1. verify;
2. expand to explicit `rewrite`/`assumption` steps with no `derive using`; and
3. replay after reparsing the expanded source.

The regression should retain only array-level loadability in the surrounding
context. Adding the exact element-loadability proposition would hide the bug.

## Acceptance criteria

- Simple goal and rewrite-premise lowering can use certified pointer equality
  to transport the existing array loadability to the aliased element.
- The restricted proof reasons only from its listed equalities; ambient facts
  may justify that the surface expressions themselves are defined, but may not
  prove the equality goal.
- The owned-segmented-buffer site migrates to `simp() using`, expands without
  `derive using`, and the project verifies within its normal budget.
- The focused regression and the default library test suite pass.
