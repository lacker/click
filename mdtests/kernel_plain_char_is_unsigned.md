# Kernel plain `char` is unsigned

The Linux kernel builds with `-funsigned-char`, so under the kernel
target the `char` holding the byte 0xC8 is 200 and `c < 0` is false.
`userspace_plain_char_is_signed.md` is the same program under the
user-space target.

```c filename=kernel_plain_char.c
int negative_byte(void) {
    char c = '\xc8';
    return c < 0;
}
```

```click
target "x86_64-linux-kernel";
verifying "kernel_plain_char.c";

int32 negative_byte() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
