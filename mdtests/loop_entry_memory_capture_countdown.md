# Loop memory footprints use the entry counter

An ordinary loop views clause acquires its physical range before the counter
is havocked. The proof includes empty input and full countdown termination.

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
pass
```
