# Unsigned division and remainder expose their nonzero-divisor obligation

```c filename=divide.c
uint32 divide(uint32 x, uint32 y) { return x / y; }
uint32 remainder(uint32 x, uint32 y) { return x % y; }
uint64 divide_wide(uint64 x, uint64 y) { return x / y; }
uint64 remainder_wide(uint64 x, uint64 y) { return x % y; }
```

```click
verifying "divide.c";
uint32 divide(uint32 x, uint32 y) {
    requires y != 0u32;
    ensures result == x / y;
} by {
    step() by { close(); }
    close();
}

uint32 remainder(uint32 x, uint32 y) {
    requires y != 0u32;
    ensures result == x % y;
} by {
    step() by { close(); }
    close();
}

uint64 divide_wide(uint64 x, uint64 y) {
    requires y != 0u64;
    ensures result == x / y;
} by {
    step() by { close(); }
    close();
}

uint64 remainder_wide(uint64 x, uint64 y) {
    requires y != 0u64;
    ensures result == x % y;
} by {
    step() by { close(); }
    close();
}
```

```expect
pass
```
