# separation extent assumption

```c filename=separation_extent_assumption.c
int32 a[1];
int32 b[1];
int32 identity(int32 n) { return n; }
```

```click
verifying "separation_extent_assumption.c";
int32 identity(int32 n) {
    requires separate(memory(a[0..n]), memory(b[0..1]));
    ensures result >= 0;
    ensures result <= 1073741823;
} by { execute(); simp(); }
```

```expect
pass
```
