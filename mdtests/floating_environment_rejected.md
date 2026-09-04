# C0 rejects floating-point environment directives

The source expander must not silently discard a floating-point environment
directive whose rounding or exception behavior is outside the C0 model.

```c filename=floating_environment_rejected.c
#pragma STDC FENV_ACCESS ON

int32 floating_environment_rejected() {
    return 0;
}
```

```click
verifying "floating_environment_rejected.c";

int32 floating_environment_rejected() {
    ensures result == 0 by auto;
}
```

```expect
fail: unsupported preprocessor directive `#pragma STDC FENV_ACCESS ON`
```
