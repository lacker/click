# Composite slice bounds survive normalization of adjacent ranges

```c filename=split_length.c
int32 split_length(int32* p, int32 n, int32 split) { return n; }
```

```click
resource slices(p: int32*, n: int32, split: int32) {
    views p[0..split];
    views p[split..n];
}

verifying "split_length.c";
int32 split_length(int32* p, int32 n, int32 split) {
    views slices(p, n, split);
    ensures 0 <= n - split;
    ensures n - split <= 1073741823;
} by {
    observe(slices(p, n, split));
    execute();
    simp();
}
```

```expect
pass
```
