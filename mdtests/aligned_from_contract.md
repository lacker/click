# Contract alignment propagates through constant displacements

`aligned(p, n)` is evidence about a pointer's formation. A parameter has no
formation visible to the callee, so the contract states it; constant byte
displacements from that base are then decided exactly, and a coarser
alignment follows from a finer one.

```c filename=aligned_from_contract.c
int32 aligned_from_contract(uint8* p) {
    return 0;
}
```

```click
verifying "aligned_from_contract.c";

int32 aligned_from_contract(uint8* p) {
    requires aligned(p, 8);
    ensures aligned(p + 8, 8);
    ensures aligned(p + 2, 2);
    ensures aligned(p + 4, 4);
    ensures aligned(p, 4);
} by {
    execute();
    simp();
}
```

```expect
pass
```
