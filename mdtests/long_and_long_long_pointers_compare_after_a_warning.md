# `long *` and `long long *` pointers compare after a warning

GCC and Clang compare pointers to `long` and `long long` with only a
warning ("comparison of distinct pointer types lacks a cast",
`-Wcompare-distinct-pointer-types`), though they refuse to convert one to the
other. Click compares the right operand as the left operand's pointer type.

```c filename=long_and_long_long_pointers_compare_after_a_warning.c
int same(long *p, long long *q) { return p == q; }
int differ(unsigned long *p, long long *q) { return p != q; }
```

```click
verifying "long_and_long_long_pointers_compare_after_a_warning.c";

int32 same(int64 *p, int64 *q) {
    requires p == q;
    ensures result == 1 by auto;
}

int32 differ(uint64 *p, int64 *q) {
    requires (uint8*)p == (uint8*)q;
    ensures result == 0 by auto;
}
```

```expect
pass
```
