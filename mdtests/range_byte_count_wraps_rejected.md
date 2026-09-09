# range byte counts must not wrap at 32 bits

```c filename=t.c
int32 symn(int32 p[], int32 n) {
    return 0;
}
```

```click
verifying "t.c";

int32 symn(int32 p[], int32 n) {
    requires loadable(p[0..1]);
    requires n == 1073741825;
    ensures loadable(p[0..n]);
}
```

```expect
fail: kernel lowering produced 0 paths
```
