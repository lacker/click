# Verify independent input-cursor initialization

## Problem

`input_cursor_shared_pipeline` originally initialized two cursors independently
over the same viewed input:

```c
input_cursor_init(left, data, length);
input_cursor_init(right, data, length);
```

During a pointer-equality repair, the second call was changed to
`input_cursor_clone(right, left)`. Cloning is a useful operation and may remain
in the project, but routing this pipeline through it avoids proving that two
ordinary initializers can independently establish metadata resources that
share the same backing view.

## Source-fidelity invariant

Equivalent helper routing is still a source change. Click must prove the call
sequence an existing program uses, rather than selecting a helper whose
postcondition exposes friendlier pointer equalities.

## Intended regression

Restore the two independent initializer calls in the shared pipeline. Reduce
any failure while retaining:

- separate cursor-owner objects;
- the same `data` and `length` arguments passed to both calls;
- independently produced cursor metadata resources;
- two persistent views of the same readable backing; and
- later mutation of one cursor without changing the other cursor or backing.

Keep a separate clone scenario so the clone contract remains covered for its
own merits.

## Likely Click work

The general fix may involve pointer-valued modular postconditions, equality
transport across call snapshots, or composition of multiple views. It must not
assume distinct pointer arguments and must keep ownership of the two cursor
objects separate from their shared read-only backing.

## Acceptance criteria

- The shared pipeline uses the original two `input_cursor_init` calls.
- Both cursors are proved to reference the same input without a clone call or
  proof-only C equality.
- Advancing the left cursor preserves the right cursor and backing view.
- Alias-negative tests continue to reject unjustified pointer equality or
  owner overlap.
- Smart certificates replay and the project stays within tactic budgets.
