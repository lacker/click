# A pointer field cannot extend a branch local's lifetime

```c filename=automatic_scope_exit_struct_alias.c
struct Holder { int32* p; };
int32 f(int32 n) {
    struct Holder h;
    if (n == 0) { int32 a[2]; a[0] = 5; h.p = &a[0]; }
    else { int32 b[2]; b[0] = 5; h.p = &b[0]; }
    return h.p[0];
}
```

```click
verifying "automatic_scope_exit_struct_alias.c";
int32 f(int32 n) { ensures result == 5; } by { execute(); simp(); }
```

```expect
fail: undefined behavior: invalid memory access
```
