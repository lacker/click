# Calls, stores and frees grow with the live heap objects

Each step over one heap object costs work proportional to how many other
heap objects are live, so a function that creates, fills and releases N
objects is quadratic. Unlike the parameter-object bugs
(`call-step-grows-with-kept-parameter-objects.md`,
`field-store-step-grows-with-owned-parameter-objects.md`), these objects live
in distinct heap blocks, so sharing one block is not the whole cause; the
fixes may share a root.

Reproduced on master `e28770b20` with `scripts/step-scaling-hunt.py`:

```c
int32 caller() {
    struct box* p0; ... struct box* pN;
    p0 = make_box(); p0->v = 0;      /* extern: produces boxed(result) */
    ...
    drop_box(p0); ...                /* extern: consumes boxed(p) */
    return 0;
}
```

with `resource boxed(p: struct box*) { owns *p; }`, each object unfolded for
its store and folded again.

```sh
python3 scripts/step-scaling-hunt.py heap_objects --sizes 4,64,256
```

At N = 64, `pi = make_box()` charges 1,535 units for the first object and
20,146 for the last; `pi->v = i` 90 and 1,454; `drop_box(pi)` 34,579 for the
first release (63 others live) falling to 4,294 for the last. At N = 256 the
largest step is 135,379 units, mean step time is 129 ms, and the proof
charges 30,743,678 units.

Partly fixed: `apply_verified_heap_allocation_delta` expanded every live
composite the caller keeps at every call, only to look for allocation
effects. It now expands them only when the callee consumed an allocation,
and no longer claims, at an unrelated call, allocations the caller's own
resources expose. At N = 64 the last `make_box` charges 7,735 units (was
20,146) and is now flat in the live objects; the whole proof charges
1,257,950 (was 2,052,254), and at N = 256, 17,885,054 (was 30,743,678) with
a largest step of 85,146 (was 135,379).

What remains (master `b1523c784` plus that fix, N = 64):

- `drop_box(pi)` still charges 22,170 units for the first release, falling
  to 4,296 for the last. About 57% is `call_kept_ownership` →
  `expand_composites_for_frame`, which expands each kept composite to
  record what the caller keeps across the call. Those ranges are recorded
  on the call's havoc edge (`CMemoryDerivation::CallHavoc`), so computing
  only the ones the havoc asks about changes what the edge records.
- `pi->v = i` grows from 94 to 1,458 units with the live objects.
- The flat `make_box` cost depends on N itself (1,975, 3,127 and 7,735
  units at N = 4, 16 and 64): it grows with the function's N declared
  locals, not with live objects.

Acceptance: a multi-size regression over `heap_objects` shows each call,
store and release step's work and time constant in the number of other live
objects, up to logarithmic factors; ownership is still checked at every
store and release; no budget or threshold is raised.
