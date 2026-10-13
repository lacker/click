# A single indexed int64 element retains its physical type

```c filename=single_wide_element_int64_views.c
int32 f(int64* a, int64 n) {
    if (a[0] < n) { return 1; }
    return 0;
}
int32 second(int64* a, int64 n) {
    if (a[1] < n) { return 1; }
    return 0;
}
```

```click
verifying "single_wide_element_int64_views.c";
int32 f(int64* a, int64 n) { views a[0]; } by { execute(); simp(); }
int32 second(int64* a, int64 n) { views a[1]; } by { execute(); simp(); }
```

```expect
pass
```
