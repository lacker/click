# Model sequential scalar volatile objects

C0 needs a small, sequential model for scalar `volatile` objects before it can
describe ordinary systems code that performs observable reads and writes. The
first slice should preserve direct scalar accesses as ordered kernel evidence
while continuing to read and write the current symbolic value. It does not
attempt to model external agents changing memory between accesses.

Concurrency, atomics, fences, signals, device protocols, pointer-qualified
aliases, arrays, and struct fields are outside this slice. The concurrency
dependent work is tracked separately in `concurrency-and-atomics.md`.

## Violated invariant

Click must not treat a supported direct scalar volatile access as an ordinary
cached memory load or store, nor erase an access that the sequential C abstract
machine requires.

## Intended regression

An unchanged C function performs repeated reads and a write through a direct
scalar volatile object. The proof must retain distinct access facts in source
order; negative regressions reject taking the object's address and qualifying
unsupported pointer, array, or aggregate forms.

## Acceptance criteria

- Direct scalar volatile metadata is preserved from C0 through function,
  global, and static-local kernel bindings.
- Each supported direct read and write emits a distinct certified execution
  fact in path order, while the modeled scalar value follows ordinary symbolic
  memory semantics.
- Unsupported aliases and aggregate shapes are rejected explicitly, and the
  positive and negative regressions pass with `scripts/check.sh`.
