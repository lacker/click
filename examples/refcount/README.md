# Refcount

This project verifies the lifecycle of a heap object whose stored reference
count agrees with the number of logical `object_ref(obj)` capabilities.

The resource body owns the allocation and object memory once for the whole
population. `count(object_ref(obj))` names the population size, and the body
fact connects that ghost quantity to `obj->refs`.

`object_init` packages a fresh allocation into the first reference.
`object_retain` increments both the stored count and the logical population.
`object_release_nonfinal` consumes one of at least two references and
decrements both counts. `object_release_final` proves that it holds the final
unit, unfolds the population, and frees its allocation.

The pipeline exercises allocation failure and the complete successful
lifecycle: initialize, retain, nonfinal release, final release, and free. The
C functions contain only the runtime implementation; all ownership adaptation
stays in the Click sidecar.
