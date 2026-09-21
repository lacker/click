# An escaped automatic object is invalid after scope exit

```c filename=automatic_scope_exit_for_init.c
int32 f() { int32* q; for (int32 i = 0; i < 1; i++) { q = &i; } return q[0]; }
```

```click
verifying "automatic_scope_exit_for_init.c";
int32 f() { ensures 0 <= result; } by { execute(); simp(); }
```

```expect
fail: undefined behavior: invalid memory access
```
