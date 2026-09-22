# separation extent composite bounds

```c filename=separation_extent_composite_bounds.c
int32 length(int32* p, int32 n) { return n; }
```

```click
verifying "separation_extent_composite_bounds.c";
resource slice(p: int32*, n: int32) { views p[0..n]; }
int32 length(int32* p, int32 n) {
    views slice(p, n);
    ensures result >= 0;
    ensures result <= 1073741823;
} by { observe(slice(p, n)); execute(); simp(); }
```

```expect
pass
```
