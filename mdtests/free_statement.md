# free statement consumes free permission

This checks the narrow executable `free(p);` statement. It consumes
`free(p[0..1])` and does not require write permission.

```c filename=release_one.c
int32 release_one(int32 p[]) {
    free(p);
    return 0;
}
```

```click
verifying "release_one.c";

int32 release_one(int32 p[]) {
    requires free(p[0..1]);

    ensures returns_zero: result == 0 by auto;
}
```

```expect
pass
```
