# Previously rejected signed char source now verifies

The original unsupported-type regression is retained unchanged. Signed bytes
now have their own modeled type and this program verifies.

```c filename=c_unmodeled_standard_type_diagnostic.c
signed char unsupported_width() {
    return 0;
}
```

```click
verifying "c_unmodeled_standard_type_diagnostic.c";

signed char unsupported_width() {
    ensures result == 0;
}
```

```expect
pass
```
