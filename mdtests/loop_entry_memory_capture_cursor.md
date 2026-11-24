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
  invariant p == old(p) + (old(n) - n);
  maintain by {
   have 0 <= to_integer(old(n) - n + 1) by close() using { 0 <= n; n <= old(n); old(n) <= 15; n > 0; };
   have to_integer(old(n) - n + 1) <= to_integer(old(n)) by close() using { 0 <= n; n <= old(n); old(n) <= 15; n > 0; };
   have 0 <= to_integer(old(n) - n) by close() using { 0 <= n; n <= old(n); old(n) <= 15; n > 0; };
   have to_integer(old(n) - n) <= 14 by close() using { 0 <= n; n <= old(n); old(n) <= 15; n > 0; };
   mark head;
   step_until(loop.back_edge);
   have p == at(head, p) + 1 by close();
   have to_integer(old(n) - n) == to_integer((old(n) - at(head, n)) + 1) by close() using {
    at(head, n) > 0; at(head, n) <= old(n); old(n) <= 15;
   };
   have p == old(p) + (old(n) - n) by {
    rewrite(p, at(head, p) + 1);
    rewrite(to_integer(old(n) - n), to_integer((old(n) - at(head, n)) + 1));
    have defined((old(n) - at(head, n)) + 1) by close();
    apply(click::integer::uint8_pointer_translate_int32(at(head, p), old(p), 0, old(n) - at(head, n), 1, (old(n) - at(head, n)) + 1));
   }
   have 0 <= n by close() using { at(head, n) > 0; at(head, n) <= old(n); old(n) <= 15; };
   have n < at(head, n) by close() using { at(head, n) > 0; at(head, n) <= old(n); old(n) <= 15; };
   have n <= old(n) by close() using { at(head, n) > 0; at(head, n) <= old(n); old(n) <= 15; };
  }
 }
}
```

```expect
pass
```
