# Character C-string requirements reach kernel-target callees

```c filename=cstr_signed_char_kernel_requirement_reaches_callee.c
int check(const signed char *src) { return 0; }
int outer(const signed char *src) {
    int result = check(src);
    return result;
}
```

```click
target "x86_64-linux-kernel";
verifying "cstr_signed_char_kernel_requirement_reaches_callee.c";
int32 check(const int8* src) {
    requires cstr_readable(src);
    ensures result == 0;
} by { execute(); simp(); }
int32 outer(const int8* src) {
    requires cstr_readable(src);
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
pass
```
