# Captured loop memory still rejects shifted access

```c filename=signed.c
int inspect(const unsigned char *p, int n) {
    while (n > 0) { n--; }
    return n;
}
```

```click
verifying "signed.c";
int32 inspect(const uint8* p, int32 n) {
 requires 0 <= n and n <= 15;
 views p[1..n + 1];
 ensures result == 0;
} by {
 loop {
  decreases n;
  views p[0..n];
  invariant 0 <= n and n <= old(n);
 }
 execute(); simp();
}
```

```expect
fail: loop declares a resource the enclosing function does not hold
```
