# separation extent unbounded goal rejected

```c filename=separation_extent_unbounded_goal_rejected.c
int32 a[1];
int32 b[1];
int32 identity(int32 n) { return n; }
```

```click
verifying "separation_extent_unbounded_goal_rejected.c";
int32 identity(int32 n) {
    ensures separate(memory(a[0..n]), memory(b[0..1]));
} by { execute(); simp(); }
```

```expect
fail: unclosed goal: separate
```
