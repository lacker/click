# Remove the runtime-allocation no-op null branch

## Problem

`examples/runtime-int32-allocation/allocate_int32s.c` currently contains:

```c
data = malloc(count * 4);
if (data == 0) {
    data = 0;
}
return data;
```

The branch assigns a null pointer to itself and has no program effect. It
appears to expose allocator success and failure as C control flow so the Click
proof can fold a conditional resource. Real allocation wrappers commonly just
return the allocator result; requiring a redundant branch is a direct adoption
failure.

## Source-fidelity invariant

Click's allocator semantics already know that allocation has success and
failure outcomes. A proof must be able to distinguish and package those
outcomes without asking the C program to branch on a value it otherwise returns
unchanged.

## Intended regression

Use the natural implementation, preserving its ordinary assignment spelling:

```c
int32* allocate_int32s(int32 count) {
    int32* data;
    data = malloc(count * 4);
    return data;
}
```

Also cover the direct `return malloc(count * 4);` spelling if it is in the C0
subset. The Click contract should return a nullable conditional resource whose
nonnull case owns the exact runtime-sized allocation and memory.

## Likely Click work

Make allocator outcome facts and conditional-resource guard selection survive
ordinary assignment and return lowering. If proof branching is needed, expose
it in Surface Click rather than manufacturing a C branch. Expansion must emit a
replayable certificate for either allocator path.

## Acceptance criteria

- The no-op branch and self-assignment are removed from the C fixture.
- The unchanged allocator result is packaged into the same nullable owning
  resource on both outcomes.
- Allocation failure, success, later use, and free remain covered.
- No proof-only C local, branch, or helper replaces the removed code.
- Direct verification, profiling, expansion, and the default test suite pass.
