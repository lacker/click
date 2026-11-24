# Signed byte swap uses a selected frame

The second store may discard the cached first cell. Its value is recovered
from the recorded store using the cited index bound, through the matching
signed-byte conversions.

```c filename=swap.c
void swap(int8* p, uint64 n) {
    int8 t = p[0];
    p[0] = p[n - 1];
    p[n - 1] = t;
}
```
```click
verifying "swap.c";
void swap(int8* p, uint64 n) {
    owns p[0u64..n];
    requires 2u64 <= n;
    requires n <= 1000u64;
    ensures p[0] == old(p[n - 1]);
} by {
    have 0u64 < n - 1u64 by { close(); }
    step_until(function.exit);
    have p[0] == old(p[n - 1]) by {
        close();
    }
}
```
```expect
pass
```
