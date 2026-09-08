# Split nested explicit post-call proof cases

## Violated invariant

A proof-level `if` introduces its two logical cases at the source position
where it is written, including inside another post-call proof case. The
deferred outcome driver currently splits the outer condition but merely
selects the inner arm, failing when the inner condition is not already known.
This is a prompt missing-proof-operation diagnostic, not a timeout or an
accepted invalid certificate.

## Intended regression

Start from `mdtests/c_contract_executes_status.md`. In `lift`, after the
successful branch's `have cell[0] == item`, insert:

```click
if item == 0 {
    have cell[0] == 0 by { simp(); }
} else {
    have cell[0] != 0 by { simp(); }
}
```

Keep `fold(Cell(cell)); frame(); simp();` after this inner conditional and
leave the failure branch unchanged. Both inner claims follow from the
established equality. Ordinary verification currently fails with
`focused outcome does not decide the post-execution if condition`.

## Acceptance criteria

- Nested explicit outcome cases verify, with checked complementary assumptions.
- Split only the outcomes reaching the written inner case; do not enumerate
  unrelated sibling cases or automatically split contract implications.
- Shared continuations, impossible arms, and asymmetric nesting have mdtests;
  corrupted branch conclusions fail.
- Expansion and audit preserve the source case structure and pass.
- Retain output-sensitive work without repeatedly cloning unrelated sibling
  execution states; add deterministic scaling coverage for any representation
  changes.
- `scripts/check.sh` passes.
