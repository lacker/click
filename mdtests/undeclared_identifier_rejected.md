# An undeclared identifier in a value position is a source error

C has no implicit declaration for a name used as a value. A name this
translation unit never declares is rejected where it is written, rather than
resolved to itself and reported much later as an unbound kernel variable.

```c filename=undeclared_identifier_rejected.c
int32 undeclared_identifier_rejected(int32 x) {
    return x + missing;
}
```

```click
verifying "undeclared_identifier_rejected.c";

int32 undeclared_identifier_rejected(int32 x) {
    ensures true by auto;
}
```

```expect
fail: use of undeclared identifier `missing`
```
