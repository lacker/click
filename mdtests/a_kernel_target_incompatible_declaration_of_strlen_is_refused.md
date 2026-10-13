# A kernel-target incompatible declaration of `strlen` is refused

Click's `x86_64-linux-kernel` target compiles hosted, without
`-ffreestanding` or `-fno-builtin`, so `strlen` names the C library
function there as in user space, and GCC 14 (`-std=gnu11 -funsigned-char
-nostdinc`) warns that `int strlen(int s);` conflicts with the built-in
function, as Clang warns of an incompatible redeclaration. (With
`-ffreestanding` neither compiler diagnoses it, since `strlen` is then an
ordinary external function.) Click refuses the declaration on both targets.

```c filename=main.c
int strlen(int s);
int length_of(int s) {
    return strlen(s);
}
```

```click
target "x86_64-linux-kernel";
verifying "main.c";

int32 length_of(int32 s) {
    ensures result >= 0;
} by {
    execute();
    simp();
}
```

```expect
fail: declaration of `strlen` has type `int32 (int32)`, which is incompatible with the C library's `size_t strlen(const char *s)`
```
