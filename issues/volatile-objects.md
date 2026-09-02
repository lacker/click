# Model volatile objects

C0 rejects the `volatile` qualifier. It currently has no read/write ordering
or observable-access semantics for memory-mapped devices, signal-shared
objects, or other volatile storage.

## Violated invariant

Click must not treat an observable volatile access as an ordinary cached memory
load or store, nor erase an access that the C abstract machine requires.

## Intended regression

An unchanged C function performs two reads and one write through a volatile
object. The proof must retain the required access order; a negative test rejects
using an ordinary memory-frame proof that treats the object as stable.

## Acceptance criteria

- Volatile objects and accesses have explicit ordering and visibility rules.
- Memory-DAG, effect, loop, and contract reasoning preserve those rules.
- The positive and negative regressions pass; `scripts/check.sh` passes.
