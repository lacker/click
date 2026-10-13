# A `size_t`-bounded viewable range past a constant 32-bit one is refused

With `n == 4u64`, `viewable(bytes[0..n])` reaches one byte past the stated
`viewable(bytes[0..3])`. The refusal records that the native
view checker did not establish the goal, instead of inferring which missing
comparison caused a failed smart construction.

```c filename=simp_refuses_wide_viewable_past_a_constant_32_bit_range.c
uint64 f(uint8 bytes[], uint64 n) {
    return 0;
}
```

```click
verifying "simp_refuses_wide_viewable_past_a_constant_32_bit_range.c";

uint64 f(uint8 bytes[], uint64 n) {
    requires viewable(bytes[0..3]);
    requires n == 4u64;

    ensures result == 0u64 by {
        have viewable(bytes[0..n]) by {
            simp();
        }
        have viewable(bytes[0..3u64]) by {
            simp();
        }
        execute();
        simp();
    }
}
```

```expect
fail: kernel native view checker did not establish
```
