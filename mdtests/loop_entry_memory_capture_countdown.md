# Loop memory footprints use the entry counter

An ordinary loop views clause acquires its physical range before the counter
is havocked. The proof includes empty input and full countdown termination.

Each decrement changes the counter alone. The proof preserves the view
with its saved bounds, then uses containment to narrow it to the new count.

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
  maintain by {
   mark before_decrement;
   step();
   have separate(loop(0).statement(0).footprint, at(before_decrement, memory(p[0..n]))) by {
    close();
   }
   have viewable(at(before_decrement, memory(p[0..n]))) by {
    preserve(at(before_decrement, memory(p[0..n])), loop(0).statement(0));
   }
   have 0 <= n by close();
   have n <= at(before_decrement, n) by close();
   apply(click::separation::contains_subrange(p, 0, at(before_decrement, n), 0, n));
   apply(click::separation::viewable_restrict(at(before_decrement, memory(p[0..n])), memory(p[0..n])));
   close();
  }
 }
}
```

```expect
pass
```
