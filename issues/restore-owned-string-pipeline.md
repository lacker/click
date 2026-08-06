# Restore the owned-string modular pipeline

## Problem

`examples/owned-string/owned_string_pipeline.c` used to exercise the natural
sequence:

```c
ignored = owned_string_init(owner, data, capacity);
ignored = owned_string_push(owner, first);
observed = owned_string_get(owner, 0);
ignored = owned_string_pop(owner);
return observed;
```

Commit `09ed72e` fixed soundness around uninitialized automatic storage, but it
also replaced that pipeline with `init`, `clear`, and `return first`. The local
`observed` in the original was assigned before it was read, so the original C
operation was not the uninitialized-read bug. The difficult modular calls and
snapshot transport were removed instead of being proved under the corrected
model.

The current README still says the project covers a pipeline of modular calls,
so the fixture and its documentation now disagree.

## Source-fidelity invariant

Fixing the semantics of uninitialized locals must not require deleting later,
well-defined uses of an assigned local or replacing a call sequence with an
easier program. The Click proof must follow the C program's actual sequence.

## Intended regression

Restore the original push/get/pop pipeline as the integration source. Before
changing the verifier, reduce any failure into mdtests that retain:

- declaration of a local without an initializer;
- assignment to that local on every path before its first read;
- a value transported through several verified opaque calls; and
- push followed by get and pop through composite-resource contracts.

Keep actual uninitialized reads rejected in the existing negative coverage.

## Likely Click work

The repair may involve automatic-local initialization state, modular call
snapshot transport, field-derived effects, or proof-surface reconstruction.
Whichever layer is responsible, fix the general rule and keep successful smart
certificates replayable. Do not add a proof-only C assignment or split the
pipeline into a different helper sequence.

## Acceptance criteria

- The original init/push/get/pop C pipeline is restored without semantic
  changes or proof-only C statements.
- Its contract proves the observed value, final empty state, and relevant
  ownership through ordinary verified call summaries.
- Assigned-before-read locals pass; genuinely uninitialized reads still fail.
- `click profile`, `click expand`, and the default test suite remain within
  their normal budgets.
- `examples/owned-string/README.md` accurately describes the restored code.
