# unmodeled standard integer widths have a useful diagnostic

The standard spellings for integer widths that Click does not model yet must
be rejected explicitly, rather than reported as an unrecognized generic type.

```c filename=c_unmodeled_standard_type_diagnostic.c
char unsupported_width() {
    return 0;
}
```

```click
verifying "c_unmodeled_standard_type_diagnostic.c";

char unsupported_width() {
    ensures result == 0;
}
```

```expect
fail: unsupported C type `char`
```
