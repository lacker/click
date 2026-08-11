# Owned-split-buffer generated rewrite is not an exact available fact

`examples/owned-split-buffer` fails ordinary verification:

```text
`owned_split_buffer_pipeline.contract` have proof 0: `rewrite` requires its
equality to be an exact available fact
```

A smart `have` proof succeeds during search, but the generated certificate
contains a `rewrite` step whose equality is not exactly available when the
certificate replays. This is a generation/replay mismatch: certificate
construction spelled the equality against a fact set that differs from the
replay-visible one. The premise-spelling invariant from the search-construction
migration (premises are spelled against `SimpleProofBuilder::certificate_facts`,
not the planning executor's transported facts) appears to be violated on this
path.

The violated invariant: a generated certificate must replay against the
replay-visible fact set; `rewrite` never searches for an equivalent equality.

## Reproduction

```sh
target/debug/click verify examples/owned-split-buffer
```

The project is quarantined in `tests/examples.rs` until this is fixed. A
reduced regression should capture the pipeline `have` whose equality is
spelled differently between construction and replay.

## Acceptance criteria

- The unchanged owned-split-buffer project verifies and leaves quarantine.
- A focused regression pins the construction-time versus replay-time spelling
  of the rewrite equality.
- The fix corrects certificate spelling; it does not add equality search to
  simple `rewrite` replay.
