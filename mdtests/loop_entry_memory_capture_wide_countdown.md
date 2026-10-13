# Loop memory footprints use the entry counter

An ordinary loop views clause acquires its physical range before the counter
is havocked. The proof includes empty input and full countdown termination.

```c filename=loop.c
unsigned long inspect(const unsigned char *p, unsigned long n) {
    while (n > 0) { n--; }
    return n;
}
```

```click
target "x86_64-linux-userspace";
verifying "loop.c";
uint64 inspect(const uint8* p, uint64 n) {
 requires n <= 15u64;
 views p[0u64..n];
 ensures result == 0u64;
} by {
 loop {
  decreases to_integer(n);
  views p[0u64..n];
  invariant to_integer(n) <= 15;
  initialize by { apply(uint64_less_equal_to_integer(n, 15u64)); simp(); }
  preserve by {
   have n > 0u64 by assumption();
   have 0u64 < n by {
    if 0u64 < n { assumption(); } else {
     have 0u64 <= n by normalize();
     apply(uint64_less_equal_and_not_less_than_implies_equal(0u64, n));
     have n == 0u64 by { rewrite(0u64 == n); normalize(); }
     have not (n > 0u64) by { rewrite(n == 0u64); normalize(); }
     contradiction(n > 0u64);
    }
   }
   apply(uint64_to_integer_bounds(n));
   apply(uint64_less_than_to_integer(0u64, n));
   have to_integer(1u64) <= to_integer(n) by arithmetic() using { to_integer(0u64) < to_integer(n); };
   apply(uint64_to_integer_less_equal_implies_less_equal(1u64, n));
   apply(uint64_subtract_to_integer(n, 1u64));
   mark before_decrement;
   step();
   have to_integer(n) == at(before_decrement, to_integer(n)) - 1 by assumption();
   have to_integer(n) <= 15 by arithmetic() using { to_integer(n) == at(before_decrement, to_integer(n)) - 1; at(before_decrement, to_integer(n)) <= 15; };
   have 0 <= to_integer(n) by arithmetic() using { to_integer(n) == at(before_decrement, to_integer(n)) - 1; to_integer(1u64) <= at(before_decrement, to_integer(n)); };
   have to_integer(n) < at(before_decrement, to_integer(n)) by arithmetic() using { to_integer(n) == at(before_decrement, to_integer(n)) - 1; };
   close_invariants by { simp(); }
  }
 }
 have n <= 0u64 by assumption();
 have not (n < 0u64) by normalize();
 apply(uint64_less_equal_and_not_less_than_implies_equal(n, 0u64));
 execute(); simp();
}
```

```expect
pass
```
