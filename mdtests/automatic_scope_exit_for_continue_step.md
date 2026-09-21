# A continue leaves the body scope before evaluating the for update

```c filename=for_step.c
int32 f() { int32* q; for (int32 i = 0; i < 1; i = q[0]) { int32 a[1]; a[0] = 1; q = &a[0]; continue; } return 1; }
```

```click
verifying "for_step.c";
int32 f() { ensures result == 1; } by { execute(); simp(); }
```

```expect
fail: undefined behavior: invalid memory access
```
