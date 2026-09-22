# Nothrow does not authorize memory writes

```c filename=nothrow.c
__attribute__((__nothrow__)) int set(int *p) {
    *p = 7;
    return *p;
}
```

```click
verifying "nothrow.c";
int set(int *p) {
    views p[0..1];
    ensures result == 7 by auto;
}
```

```expect
fail: missing resource fact
```
