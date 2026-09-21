# An escaped automatic object is invalid after scope exit

```c filename=automatic_scope_exit_nested_branch.c
int32 f(int32 n) { int32* q; int32 z; if (n == 0) { int32 a[2]; a[0] = 5; if (n == 0) q = &a[0]; else q = &a[1]; } else { int32 b[2]; b[0] = 5; q = &b[0]; } z = q[0]; return z; }
```

```click
verifying "automatic_scope_exit_nested_branch.c";
int32 f(int32 n) { ensures 0 <= result; } by { execute(); simp(); }
```

```expect
fail: undefined behavior: invalid memory access
```
