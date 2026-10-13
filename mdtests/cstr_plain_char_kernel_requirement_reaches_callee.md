# Character C-string requirements reach kernel-target callees

```c filename=cstr_plain_char_kernel_requirement_reaches_callee.c
int check(const char *src) { return 0; }
int outer(const char *src) {
    int result = check(src);
    return result;
}
```

```click
target "x86_64-linux-kernel";
verifying "cstr_plain_char_kernel_requirement_reaches_callee.c";
int32 check(const char* src) {
    requires cstr_readable(src);
    ensures result == 0;
} by { execute(); simp(); }
int32 outer(const char* src) {
    requires cstr_readable(src);
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
pass
```
