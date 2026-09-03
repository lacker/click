# Match heap frees against every owned allocation authority

Found while verifying the arena destructor on 2026-09-02. The heap-free
executor searched for an allocation authority with `find_map` and only then
checked whether its base matched the pointer being freed. A resource context
holding two allocation authorities therefore could not free the second one:
the executor reported a non-heap pointer even though the matching authority
was present.

## Violated invariant

`free(p)` must use the allocation authority whose base is `p`, regardless of
where that authority appears among the other live allocation resources. It
must not depend on resource iteration order or accidentally treat an owned
allocation as a non-heap pointer.

## Intended regression

An mdtest declares a struct containing two independently allocated `int32`
buffers, gives a function both allocation authorities and complete owned
ranges, and frees the second buffer before the first. The function must
verify. A missing-authority variant must still fail at `free`, so the fix must
not make arbitrary external pointers heap allocations.

## Acceptance criteria

- Heap-free lookup filters allocation authorities by the evaluated pointer
  before selecting one.
- The positive multi-allocation regression and a missing-authority negative
  regression pass.
- Existing heap, resource, and full verification gates remain green.
