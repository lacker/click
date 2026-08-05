# Authorize `free` effects from owned allocation resources

## Problem

With runtime-sized allocation ownership unfolded in `vector_grow`, exact
symbolic execution performed a direct `free(old_data)` but failed the contract's
effect claim (`Effect(0)`). The contract owned the exact allocation authority
and complete memory range, yet the effect checker did not recognize retirement
of that owned heap lifetime as authorized. Routing the operation through an
opaque `vector_free` helper avoided the immediate check, but that is not an
acceptable requirement on real C code.

Click is intended to verify awkward existing C. Direct `free` must work whenever
the resource preconditions establish the authority required by the memory
model.

## Intended design

- Treat consuming `owns allocation(base, bytes)` plus complete access to its
  cells as authority for the heap-lifetime transition at `free(base)`.
- Keep this distinct from mutable byte ranges: retirement changes allocation
  validity, not merely stored values.
- Include the lifetime effect in exact execution/certification in a stable,
  symbolic-size-aware form.
- Continue to reject partial access, interior pointers, double free, and
  surviving nonseparated resources.

## Regression

Add an mdtest that owns a runtime-sized `int32` allocation and frees it directly
inside a larger function with unrelated surviving resources. The exact
contract effect must certify without a wrapper call. Negative companions should
cover missing allocation authority and incomplete cell ownership.

## Acceptance criteria

- Direct `free` certifies under exact owned allocation resources.
- No `mutable allocation(...)` surface workaround or helper function is needed.
- Symbolic sizes and external argument bases behave like fixed struct
  allocations.
- Existing invalid-free and survivor-separation tests remain green.
