# User-space plain `char` is signed

Under `x86_64-linux-userspace`, plain `char` is signed, as GCC and Clang
build it for the x86-64 System V ABI. The character constant `'\xc8'` is a
`char` holding the byte 0xC8, which is -56, so `c < 0` holds.
`kernel_plain_char_is_unsigned.md` is the same program under the kernel
target, which builds with `-funsigned-char`.

```c filename=userspace_plain_char.c
int negative_byte(void) {
    char c = '\xc8';
    return c < 0;
}
```

```click
target "x86_64-linux-userspace";
verifying "userspace_plain_char.c";

int32 negative_byte() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
