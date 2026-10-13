# A moving cursor retains the loop-entry footprint

Both pointer and count are modified. The ordinary views clause still acquires
the original physical range; it does not claim a new range at each cursor.

```c filename=cursor.c
int cursor(const unsigned char *p, int n) { while (n > 0) { p++; n--; } return n; }
```

```click
verifying "cursor.c";
int32 cursor(const uint8* p, int32 n) {
 requires 0 <= n and n <= 15;
 views p[0..n];
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
pass
```
