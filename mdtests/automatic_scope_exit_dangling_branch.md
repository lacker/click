# A branch local cannot be read after its scope ends

The alias escapes either branch, but its automatic object does not.

```c filename=automatic_scope_exit_dangling_branch.c
int32 f(int32 n) {
    int32* q; int32 z;
    if (n == 0) { int32 a[2]; a[0] = 5; q = &a[0]; }
    else { int32 b[2]; b[0] = 5; q = &b[0]; }
    z = q[0];
    return z;
}
```

```click
verifying "automatic_scope_exit_dangling_branch.c";
int32 f(int32 n) {
    ensures result == 5;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior: invalid memory access
```
