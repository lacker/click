# Reject an uninitialized automatic array element selected symbolically

```c filename=t.c
int32 local_sym(int32 i) {
    int32 a[3];
    a[0] = 1;
    a[1] = 2;
    return a[i];
}
```

```click
verifying "t.c";
int32 local_sym(int32 i) {
    requires i == 2;
    ensures result == result;
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
