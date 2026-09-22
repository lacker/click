# separation extent call

```c filename=separation_extent_call.c
int32 a[1];
int32 b[1];
int32 identity(int32 n) { return n; }
int32 caller(int32 n) { return identity(n); }
```

```click
verifying "separation_extent_call.c";
int32 identity(int32 n) {
    requires separate(memory(a[0..n]), memory(b[0..1]));
    ensures result >= 0;
    ensures result <= 1073741823;
} by { execute(); simp(); }
int32 caller(int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    ensures result >= 0;
} by { execute(); simp(); }
```

```expect
pass
```
