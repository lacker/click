# Observe one held memory range after a write

```c filename=observe_memory.c
void update(int32 p[], int32 n) { p[0] = 9; }
```

```click
verifying "observe_memory.c";
void update(int32 p[], int32 n) {
    owns p[0..n];
    requires 0 < n;
    ensures viewable(p[0..n]);
} by {
    step_until(function.exit);
    have viewable(p[0..n]) by { observe(p[0..n]); }
    close();
}
```

```expect
pass
```
