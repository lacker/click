# Contributing to Click

Most Click changes should start from a proof need, not from an isolated syntax
idea.

The default workflow is:

1. Find the smallest nearby mdtest.
2. Add or change a test that shows the desired behavior.
3. Confirm the expected failure.
4. Implement the smallest parser, lowering, kernel, or prover change.
5. Add unit tests if the change is below the mdtest level.
6. Run the relevant tests, then `cargo test`.
7. Update the docs.

The feature playbook is the detailed checklist.

## Where new concepts belong

Prefer this order:

1. An ordinary Click definition in `stdlib/prelude.click`.
2. Deterministic proof support for a general pattern.
3. A new tactic if users need explicit control.
4. New syntax only when existing syntax cannot express the concept clearly.

This keeps the language smaller and makes kernel support more reusable.

## Contributor reading path

If you are changing Click itself, read:

1. the beginner chapters, to understand the user-facing model,
2. the intermediate chapters, to understand the proof concepts,
3. the feature playbook, for the implementation workflow,
4. the kernel internals page, for Rust module boundaries,
5. the proof landscape and roadmap, for feature prioritization.

## Documentation ownership

The beginner chapters should optimize for teaching and trust. They may be
rewritten by humans over time.

The intermediate chapters should connect examples to concepts and stay accurate
as features grow.

The advanced and reference chapters should stay close to the implementation.
They should be updated whenever tests, lowering, kernel behavior, or roadmap
assumptions change.

## Working conventions (from the 2026-07 performance-tools project)

- Gates: `cargo nextest run --lib --bins` (the `--bins` matters — CLI
  `#[cfg(test)]` modules are not covered by `--lib` alone),
  `cargo test --test mdtests`, `cargo test --test examples`. Keep
  master green; commit in small validated steps.
- Probe pattern: env-gated eprintln/file dumps at the failing check,
  run under a filter, strip probes before committing.
- Guard and depth-gate any new recursive prover arm; structural
  recursion on deep terms has overflowed the stack before.
- SOUNDNESS TRAP: never drop havoc/call-havoc blocks from canonical
  load memories; kernel test
  `memory_load_equality_does_not_ignore_loop_havoc_identity` guards it.
- Reproduce stale timing claims before acting on them; slow-but-passing
  is a reportable finding, not a resting state.
- Known bugs and pending decisions live in `issues/`, one file each.
