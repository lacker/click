# An escaped automatic object is invalid after scope exit

```c filename=automatic_scope_exit_loop_break.c
int32 f() { int32* q; while (1) { int32 a[2]; a[0] = 5; q = &a[0]; break; } return q[0]; }
```

```click
verifying "automatic_scope_exit_loop_break.c";
int32 f() { ensures 0 <= result; } by { execute(); simp(); }
```

```expect
fail: undefined behavior: invalid memory access
```
