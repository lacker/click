# external function contracts carry memory effects

```c filename=caller.c
int32 caller(int32 p[]) {
    int32 ignored;
    ignored = external_set(p);
    return p[0];
}
```

```click
verifying "caller.c";

extern int32 external_set(int32 p[]) {
    owns p[0..1];
    mutable p[0..1];
    ensures p[0] == 0;
    ensures result == 0;
}

int32 caller(int32 p[]) {
    owns p[0..1];
    ensures result == 0;
}
```

```expect
pass
```
