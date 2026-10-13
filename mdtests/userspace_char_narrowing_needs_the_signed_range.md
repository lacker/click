# Converting to user-space `char` needs the signed byte range

C0 refuses an out-of-range conversion to a signed integer type rather than
choosing the implementation-defined result. User-space plain `char` is
signed, so converting 200 to `char` owes the `int8` narrowing bound and is
refused, where the kernel target's unsigned `char` holds 200.

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
    ensures result == 200;
} by {
    execute();
    simp();
}
```

```expect
fail: int8 narrowing upper bound
```
