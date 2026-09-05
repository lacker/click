# Alignment must be a power of two

`aligned(p, n)` masks the low address bits, which only describes alignment
when `n` is a power of two. Any other constant is rejected at parse time.

```c filename=aligned_rejects_non_power_of_two.c
int32 aligned_rejects_non_power_of_two(uint8* p) {
    return 0;
}
```

```click
verifying "aligned_rejects_non_power_of_two.c";

int32 aligned_rejects_non_power_of_two(uint8* p) {
    requires aligned(p, 6);
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: aligned expects a power-of-two byte alignment
```
