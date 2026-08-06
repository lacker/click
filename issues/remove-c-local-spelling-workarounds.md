# Remove C-local spelling workarounds

## Problem

Commit `14aed95` repaired modular call snapshot transport while also renaming a
local variable from `result` to `read_value` in both:

- `owned_segmented_buffer_pipeline.c`;
- `owned_split_buffer_pipeline.c`.

The rename does not change C behavior. Other current fixtures successfully use
locals named `result`, so these edits are now at least stale and may record a
past collision between an ordinary C identifier and Click's contract-level
`result` spelling. Leaving them in place hides whether snapshot transport is
actually independent of local names.

## Source-fidelity invariant

An existing C identifier is part of the accepted source. Click's parser,
lowering, proof snapshots, and diagnostics must distinguish a C local from the
contract result value by scope, not by asking users to rename the local.

## Intended regression

Restore `int32 result;`, assignment to `result`, and `return result;` in both
pipelines. Add a focused mdtest in which:

- a C local is named `result`;
- it receives an opaque call's return value;
- later calls mutate related composite resources; and
- the function returns the local while the Click contract also mentions its
  own `result` pseudo-value.

The mdtest should make both bindings observable so an accidental name capture
cannot pass vacuously.

## Acceptance criteria

- Both pipeline C files verify with their original `result` local spelling.
- Surface Click resolves C locals and the function-result pseudo-value by the
  correct scope at every program point.
- Snapshot transport and generated certificates do not depend on renaming the
  local.
- Diagnostics clearly distinguish the two bindings.
- Parser, lowering, mdtest, example, expansion, and audit coverage pass.
