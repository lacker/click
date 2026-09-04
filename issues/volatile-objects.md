# Model sequential scalar and pointer-qualified volatile objects

C0 needs a small, sequential model for scalar `volatile` objects and
one-level pointers to them before it can describe ordinary systems code that
performs observable reads and writes. Direct scalar accesses and pointer-
derived scalar accesses should remain ordered kernel evidence while continuing
to read and write the current symbolic value. The model does not attempt to
represent external agents changing memory between accesses.

Concurrency, atomics, fences, signals, device protocols, pointer-to-pointer
qualifiers, volatile array objects, volatile struct fields, and volatile
function-pointer objects are outside this slice. The concurrency-dependent
work is tracked separately in `concurrency-and-atomics.md`.

## Violated invariant

Click must not treat a supported direct or pointer-derived scalar volatile
access as an ordinary cached memory load or store, nor erase an access that the
sequential C abstract machine requires.

## Intended regression

An unchanged C function takes the address of a scalar volatile object and
performs repeated reads and a write through a pointer alias. The proof must
retain distinct access facts in source order; negative regressions reject
unsupported pointer depth and aggregate forms.

## Acceptance criteria

- Direct scalar and pointer-qualified volatile metadata is preserved from C0
  through function and local kernel bindings.
- Address-of, pointer arithmetic, dereference, and indexed scalar accesses
  preserve one ordered access fact per read or write, while the modeled value
  follows ordinary symbolic memory semantics.
- Unsupported pointer depth and aggregate shapes are rejected explicitly, and
  the positive and negative regressions pass with `scripts/check.sh`.
