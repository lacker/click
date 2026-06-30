# free does not require write permission

This checks that executable `free(p);` uses deallocation authority, not write
authority.

```c filename=free_without_write.c
int32 free_without_write(int32 p[]) {
    free(p);
    return 0;
}
```

```click
verifying "free_without_write.c";

int32 free_without_write(int32 p[]) {
    requires free(p[0..1]);

    ensures returns_zero: result == 0 by auto;
}
```

```expect
pass
```
