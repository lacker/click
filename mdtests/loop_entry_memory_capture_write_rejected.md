# Captured loop memory still rejects write access

```c filename=signed.c
int inspect(unsigned char *p, int n) {
    while (n > 0) { p[0] = 0; n--; }
    return n;
}
```

```click
verifying "signed.c";
int32 inspect(uint8* p, int32 n) {
 requires 0 <= n and n <= 15;
 views p[0..n];
 ensures result == 0;
} by {
 loop {
  decreases n;
  views p[0..n];
  invariant 0 <= n and n <= old(n);
  invariant viewable(p[0..n]);
 }
 execute(); simp();
}
```

```expect
fail: missing resource fact
```
