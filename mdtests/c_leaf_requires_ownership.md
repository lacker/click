# Leaf does not grant write ownership

```c filename=leaf.c
__attribute__((leaf)) int set(int *p) {
    *p = 7;
    return *p;
}
```

```click
verifying "leaf.c";
int set(int *p) {
    views p[0..1];
    ensures result == 7 by auto;
}
```

```expect
fail: missing resource fact
```
