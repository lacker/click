# Feature playbook

Use this workflow when extending Click.

## Default process

1. Freeze the C behavior that motivated the work. If it came from an existing
   project or example, keep that source unchanged as the integration
   regression.
2. Find or reduce the smallest mdtest that preserves the awkward semantic
   pattern; do not make the reduction pass by changing the C pattern away.
3. Run `cargo test --test mdtests` and confirm the expected failure.
4. Implement the smallest contract/library/parser/lowering/kernel/prover
   change that makes the original behavior provable.
5. Add unit tests when the behavior is lower-level than an mdtest can show.
6. Reverify the unchanged integration source as well as the reduction.
7. Run focused checks that fit the change; `scripts/check.sh` is the full gate,
   which the PR workflow and merge queue run for code changes.
8. Update docs in this directory.

## C-source fidelity

Click is intended for adoption in codebases that cannot be reorganized around
the verifier. Do not repair a proof by adding no-op C, changing a local name,
splitting or combining helpers, replacing one call sequence with an easier
one, or weakening the behavior under test. Such a change is a Click issue even
when the resulting C is valid and the proof becomes green.

Changing C is appropriate when the change is independently part of the
program's desired behavior, fixes actual C undefined behavior, or performs a
documented semantics-preserving C desugaring. State which exception applies in
the change description. Otherwise, preserve the C and fix the proof boundary.

## Where a feature belongs

Prefer this order:

1. Ordinary Click definition in a `library/` module.
2. Deterministic proof support in the kernel for a general pattern.
3. New tactic if users need explicit control.
4. New syntax only when the concept cannot be expressed clearly with existing
   syntax.

Do not put every useful standard function into the kernel. Kernel support should
be for general reasoning, not names like `permutation` unless there is no better
abstraction.

## Adding Click syntax

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
  - old-state spec elaboration
  - loop invariants, or explicitly reject with a clear diagnostic
- Add mdtests and docs.

Search for all matches on:

```console
rg -n "ClickProposition|ContractExpression" src/surface.rs
```

## Adding C syntax

Checklist:

- Add parser support in `src/languages/c/syntax.rs`.
- Lower to existing kernel terms if possible.
- Add new kernel semantic terms only when needed.
- Add undefined-behavior obligations if C semantics require them.
- Add C parser unit tests and mdtests.
- Update [Supported C](../reference/language/c.md).

## Adding proof power

Prefer deterministic, narrow rules. Good examples:

- normalize one term form
- decide one equality pattern
- expose one loop effect summary
- instantiate one finite quantified pattern

Avoid broad heuristic search unless it lives behind `close()` or the implicit
closer, advances proof
state only through checked operations, and retains surface-expressible
evidence when possible.

## Adding standard library definitions

This checklist is for a pure specification module, such as `click::list`. To
support a function or type of a library the verified code calls, follow
[library interfaces](../concepts/library-interfaces.md) instead.

Checklist:

- Add source to the `library/` module for its topic.
- Add an mdtest that imports it implicitly.
- If the proof needs special support, add general kernel support and unit tests.
- Update the [standard-library reference](../reference/library/index.md).

## Updating README

Do not put long technical reference material in the root README. Keep the
human-owned manifesto intact, and keep the AI-editable section as an index into
`docs/`.
