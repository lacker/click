# A 32-bit byte range supplies the same view at a `size_t` bound

The constant endpoints describe the same three bytes at either index width.
The proof establishes containment for the constant wide range and uses
`n == 3u64` to prove containment for the symbolic wide range. Both views
follow from the original 32-bit range.

```c filename=solve_proves_wide_viewable_from_a_constant_32_bit_range.c
uint64 f(uint8 bytes[], uint64 n) {
    return 0;
}
```

```click
verifying "solve_proves_wide_viewable_from_a_constant_32_bit_range.c";

uint64 f(uint8 bytes[], uint64 n) {
    requires viewable(bytes[0..3]);
    requires n == 3u64;

    ensures result == 0u64 by {
        have contains(memory(bytes[0..3]), memory(bytes[0..3u64])) by {
            normalize();
        }
        have viewable(memory(bytes[0..3u64])) by {
            apply(click::separation::viewable_restrict(memory(bytes[0..3]), memory(bytes[0..3u64])));
            close();
        }
        have contains(memory(bytes[0..3]), memory(bytes[0..n])) by {
            rewrite(n, 3u64);
            close();
        }
        have viewable(memory(bytes[0..n])) by {
            apply(click::separation::viewable_restrict(memory(bytes[0..3]), memory(bytes[0..n])));
            close();
        }
        step();
        close();
    }
}
```

```expect
pass
```
