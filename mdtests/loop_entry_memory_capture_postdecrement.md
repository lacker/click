# A postdecrement guard keeps its consumed value and entry memory

This is zlib's `while (len--)` control-flow shape. Every positive iteration
decreases the native uint64 counter, and the final guard consumes zero while
storing UINT64_MAX before breaking. The ranked loop proves termination for
all counts up to fifteen and acquires the original byte view before havoc.

```c filename=post.c
unsigned long post(const unsigned char *p, unsigned long n) { while (n--) {} return n; }
```

```click
target "x86_64-linux-userspace";
verifying "post.c";
uint64 post(const uint8* p, uint64 n) {
 requires n <= 15u64;
 views p[0u64..n];
 ensures result == 18446744073709551615u64;
} by {
 loop {
  decreases to_integer(n);
  views p[0u64..n];
  invariant to_integer(n) <= 15;
  initialize by { apply(uint64_less_equal_to_integer(n, 15u64)); simp(); }
  preserve by {
   if n == 0u64 {
    step(); step(); step(); step();
    have __click_call_result0 == 0u64 by assumption();
    have n == 18446744073709551615u64 by { rewrite(__click_call_result0 == 0u64); normalize(); }
    step();
   } else {
    have 0u64 <= n by normalize();
    have 0u64 < n by {
     if 0u64 < n { assumption(); } else {
      apply(uint64_less_equal_and_not_less_than_implies_equal(0u64, n));
      have n == 0u64 by { rewrite(0u64 == n); normalize(); }
      contradiction(n == 0u64);
     }
    }
   apply(uint64_to_integer_bounds(n));
   apply(uint64_less_than_to_integer(0u64, n));
   have to_integer(1u64) <= to_integer(n) by arithmetic() using { to_integer(0u64) < to_integer(n); };
   apply(uint64_to_integer_less_equal_implies_less_equal(1u64, n));
   apply(uint64_subtract_to_integer(n, 1u64));
   step(); step();
   mark before_decrement;
   step(); step(); step();
   have to_integer(n) == at(before_decrement, to_integer(n)) - 1 by assumption();
   have to_integer(n) <= 15 by arithmetic() using { to_integer(n) == at(before_decrement, to_integer(n)) - 1; at(before_decrement, to_integer(n)) <= 15; };
   have 0 <= to_integer(n) by arithmetic() using { to_integer(n) == at(before_decrement, to_integer(n)) - 1; to_integer(1u64) <= at(before_decrement, to_integer(n)); };
   have to_integer(n) < at(before_decrement, to_integer(n)) by arithmetic() using { to_integer(n) == at(before_decrement, to_integer(n)) - 1; };
   execute_until(back_edge());
   close_invariants by { simp(); }
   }
  }
 }
 execute(); simp();
}
```

```expect
pass
```
