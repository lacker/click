# Scope retirement preserves valid reads and returned values

The returned scalar survives its local object's lifetime. An outer local
survives either inner branch, and a new loop iteration gets a fresh local.

```c filename=automatic_scope_exit_valid_paths.c
int32 branch_return(int32 n) {
    if (n == 0) { int32 a[2]; a[0] = 5; return a[0]; }
    else { int32 b[2]; b[0] = 5; return b[0]; }
}
int32 outer_survives(int32 n) {
    int32 a[2]; a[0] = 5;
    if (n == 0) { int32 b[2]; b[0] = 8; }
    else { int32 c[2]; c[0] = 9; }
    return a[0];
}
int32 reentry() {
    int32 i; int32 z; i = 0; z = 0;
    while (i < 2) { int32 a[2]; a[0] = 5; z = a[0]; i = i + 1; }
    return z;
}
int32 nested_empty(int32 n) {
    if (n == 0) { int32 a[2]; a[0] = 5; if (n != 0) return 1; }
    return 5;
}
```

```click
verifying "automatic_scope_exit_valid_paths.c";
int32 branch_return(int32 n) { ensures result == 5; } by { execute(); simp(); }
int32 outer_survives(int32 n) { ensures result == 5; } by { execute(); simp(); }
int32 reentry() { ensures result == 5; } by { execute(); simp(); }
int32 nested_empty(int32 n) { ensures result == 5; } by { execute(); simp(); }
```

```expect
pass
```
