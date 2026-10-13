# A single indexed uint64 element retains its physical type

```c filename=single_wide_element_uint64_views.c
int32 f(uint64* a, uint64 n) {
    if (a[0] < n) { return 1; }
    return 0;
}
int32 second(uint64* a, uint64 n) {
    if (a[1] < n) { return 1; }
    return 0;
}
```

```click
verifying "single_wide_element_uint64_views.c";
int32 f(uint64* a, uint64 n) { views a[0]; } by { execute(); simp(); }
int32 second(uint64* a, uint64 n) { views a[1]; } by { execute(); simp(); }
```

```expect
pass
```
