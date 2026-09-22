# separation extent bounded goal

```c filename=separation_extent_bounded_goal.c
int32 a[1];
int32 b[1];
int32 identity(int32 n) { return n; }
```

```click
verifying "separation_extent_bounded_goal.c";
int32 identity(int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    ensures separate(memory(a[0..n]), memory(b[0..1]));
} by { execute(); simp(); }
```

```expect
pass
```
