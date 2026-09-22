# Separation cannot claim an unchecked wrapping endpoint

```c filename=separation_extent_wrapped_endpoint_rejected.c
int32 a[1];
int32 b[1];
int32 identity(int32 n) { return n; }
```

```click
verifying "separation_extent_wrapped_endpoint_rejected.c";
int32 identity(int32 n) {
    ensures separate(memory(a[n..n + 2]), memory(b[0..1]));
} by { execute(); simp(); }
```

```expect
fail: unclosed goal: separate
```
