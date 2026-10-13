# A kernel `char` parameter is never negative

Under the kernel target plain `char` is unsigned, so `c < 0` never holds.
`userspace_char_parameter_may_be_negative.md` refuses the same claim under
the user-space target.

```c filename=kernel_char_parameter.c
int is_negative(char c) {
    return c < 0;
}
```

```click
target "x86_64-linux-kernel";
verifying "kernel_char_parameter.c";

int32 is_negative(char c) {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
