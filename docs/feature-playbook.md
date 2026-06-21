# Feature Playbook

Use this workflow when extending Click.

## Default Process

1. Find the smallest existing mdtest near the desired behavior.
2. Add or modify an mdtest that demonstrates the new proof or diagnostic.
3. Run `cargo test --test mdtests` and confirm the expected failure.
4. Implement the smallest parser/lowering/kernel/prover change.
5. Add unit tests when the behavior is lower-level than an mdtest can show.
6. Run `cargo test`.
7. Update docs in this directory.

## Where A Feature Belongs

Prefer this order:

1. Ordinary Click definition in `stdlib/prelude.click`.
2. Deterministic proof support in the kernel for a general pattern.
3. New proof step if users need explicit control.
4. New syntax only when the concept cannot be expressed clearly with existing
   syntax.

Do not put every useful standard function into the kernel. Kernel support should
be for general reasoning, not names like `permutation` unless there is no better
abstraction.

## Adding Click Syntax

Checklist:

- Extend the AST enum.
- Parse it.
- Validate names and arity.
- Substitute through it.
- Collect function calls through it.
- Lower/evaluate it in every relevant context:
  - requirements
  - predicate bodies
  - outcomes/postconditions
  - old-state evaluation
  - loop invariants, or explicitly reject with a clear diagnostic
- Add mdtests and docs.

Search for all matches on:

```sh
rg -n "ClickProposition|ContractExpression" src/lang/click.rs
```

## Adding C0 Syntax

Checklist:

- Add parser support in `src/lang/c/syntax.rs`.
- Lower to existing megakernel terms if possible.
- Add new megakernel semantic terms only when needed.
- Add undefined-behavior obligations if C semantics require them.
- Add C parser unit tests and mdtests.
- Update [c0-subset.md](c0-subset.md).

## Adding Proof Power

Prefer deterministic, narrow rules. Good examples:

- normalize one term form
- decide one equality pattern
- expose one loop effect summary
- instantiate one finite quantified pattern

Avoid broad heuristic search unless it lives behind `auto` and successful cases
can still produce replayable proof steps when possible.

## Adding Standard Library Definitions

Checklist:

- Add source to `stdlib/prelude.click`.
- Add an mdtest that imports it implicitly.
- If the proof needs special support, add general kernel support and unit tests.
- Update [standard-library.md](standard-library.md).

## Updating README

Do not put long technical reference material in the root README. Keep the
human-owned manifesto intact, and keep the AI-editable section as an index into
`docs/`.
