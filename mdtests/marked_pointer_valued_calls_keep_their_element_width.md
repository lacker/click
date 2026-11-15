# Pointer-valued calls retain their pointee size through states

```c filename=marked_pointer.c
void unchanged(uint8* p, uint32* q) {}
```

```click
verifying "marked_pointer.c";

function pointer<T>(p: T*) -> T* { p }

void unchanged(uint8* p, uint32* q) {
    ensures 0 == 0;
} by {
    mark before;
    have at(before, pointer(p)) + 1u64 == pointer(p) + 1u64;
    have at(before, pointer(q)) + 1u64 == pointer(q) + 1u64;
    have old(pointer(p)) + 1u64 == pointer(p) + 1u64;
    have old(pointer(q)) + 1u64 == pointer(q) + 1u64;
    step_until(function.exit);
}
```

```expect
pass
```
