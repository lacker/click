# A wide viewable range does not cover an element outside it

The guard `k < n + 2u64` admits `k == n + 1`, just past the end of
`bytes[0..n + 1u64]`. The proof stops at the strict upper bound required
for element containment. A separate initializedness premise would still
be needed for an element inside the range.

```c filename=wide_viewable_element_outside.c
uint64 f(uint8 bytes[], uint64 n) {
    uint64 x;
    x = 0;
    return x;
}
```

```click
verifying "wide_viewable_element_outside.c";

uint64 f(uint8 bytes[], uint64 n) {
    requires n < 18446744073709551615u64;
    requires viewable(bytes[0..n + 1u64]);
    ensures result == 0u64 by {
        step();
        have forall (k: uint64) { k < n + 2u64 implies defined(bytes[k]) } by {
            intro();
            intro();
            have 0u64 <= k by { normalize(); }
            have to_integer(k) < to_integer(n + 1u64) by { known(); }
            have contains(memory(bytes[0u64..n + 1u64]), memory(bytes[k])) by {
                apply(click::separation::contains_element(bytes, 0u64, n + 1u64, k));
            }
            known();
        }
    }
}
```

```expect
fail: `known()` could not close the current goal
```
