# One wide element grants no neighboring element

```c filename=single_wide_element_rejects_unowned_neighbor.c
uint64 f(uint64* a) { return a[1]; }
```

```click
verifying "single_wide_element_rejects_unowned_neighbor.c";
uint64 f(uint64* a) { owns a[0]; } by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
