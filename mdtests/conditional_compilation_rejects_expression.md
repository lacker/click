# Unsupported conditional expressions are rejected

The conditional subset does not evaluate general C preprocessor expressions.
An active comparison must receive a source-positioned diagnostic instead of
being guessed or silently treated as false.

```c filename=main.c
#if defined(FEATURE) == 1
int32 run() {
    return 1;
}
#endif
```

```click
verifying "main.c";

int32 run() {
    ensures result == 1;
}
```

```expect
fail: unsupported conditional expression
```
