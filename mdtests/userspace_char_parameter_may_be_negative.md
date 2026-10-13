# A user-space `char` parameter may be negative

A plain `char` parameter ranges over the target's plain `char` values.
Under the user-space target that includes the negative bytes, so a claim
that `c < 0` never holds is refused; under the kernel target
(`kernel_char_parameter_is_never_negative.md`) the same claim verifies.

```c filename=userspace_char_parameter.c
int is_negative(char c) {
    return c < 0;
}
```

```click
target "x86_64-linux-userspace";
verifying "userspace_char_parameter.c";

int32 is_negative(char c) {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == 0` failed for `is_negative.ensures_0`
```
