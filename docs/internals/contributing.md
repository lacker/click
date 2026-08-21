# Contributing to Click

Most Click changes should start from a proof need, not from an isolated syntax
idea.

The default workflow is:

1. Find the smallest nearby mdtest.
2. Add or change a test that shows the desired behavior.
3. Confirm the expected failure.
4. Implement the smallest parser, lowering, kernel, or prover change.
5. Add unit tests if the change is below the mdtest level.
6. Update the relevant reference entry and public-surface inventory.
7. Run focused tests, then run `scripts/check.sh` unpiped.

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

1. [What Click proves](../concepts/what-click-proves.md), for the user-facing
   boundary;
2. the relevant [concept page](../concepts/index.md), for the mental model;
3. the relevant [technical reference](../reference/index.md), for the public
   contract;
4. the [feature playbook](feature-playbook.md), for the change workflow;
5. [Architecture](architecture.md) and [Kernel](kernel.md), for module and
   trust boundaries.

## Documentation ownership

The technical reference, concepts, and internals in this site are intentionally
AI-written and AI-maintained. Keep them factual, exhaustive, source-backed, and
consistent with the local [documentation style](../style.md). Update the
machine-readable inventory or fixture mapping whenever a public surface
changes. The future human-written guide is a separate work with its own voice;
don't move or rewrite it as part of technical-reference maintenance without
explicit authorization.

## Working conventions

- Gate: `scripts/check.sh` is the only green-tree verdict, and CI runs the same
  script. Run it unpiped. It covers formatting, documentation, library and
  binary tests, mdtests, and examples, using nextest when available.
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
