# Converting to user-space `char` wraps into the signed byte range

User-space plain `char` is signed, so converting 200 to `char` reduces it
modulo 256 into `-128..127`, as GCC and Clang do: the result is -56, where
the kernel target's unsigned `char` holds 200. No range is owed.

```c filename=userspace_char_narrowing.c
int narrow(int x) {
    char c = (char)x;
    return c;
}
```

```click
target "x86_64-linux-userspace";
verifying "userspace_char_narrowing.c";

int32 narrow(int32 x) {
    requires x == 200;
    ensures result == -56;
} by {
    execute();
    simp();
}
```

```expect
pass
```
