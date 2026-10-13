# Typed prefix geometry without backing access

The helper may form the one-past pointer without reading or owning the elements.
The caller's array is intentionally uninitialized.

```c filename=valid_place_prefix.c
int* end_of_range(int* p, unsigned long n) { return p + n; }
int caller(void) {
    int values[3];
    return end_of_range(values, 3) == values + 3;
}
```

```click
verifying "valid_place_prefix.c";
int32* end_of_range(int32* p, uint64 n) {
    requires 1u64 <= n;
    requires valid_place(p[0..n]);
    ensures result == p + n;
} by { execute(); simp(); }
int32 caller() {
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
