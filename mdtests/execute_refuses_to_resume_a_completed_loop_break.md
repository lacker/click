# Function-exit stepping refuses a completed loop-control path

The original unsigned guard consumes the old value and decrements on every
test, including the final false test. Its lowering introduces a consumed-value
carrier and a break path. In a written preservation proof, the arm where the
facts select that break path (`n == 0u64`) asks `step_until(function.exit)` to
run on to function exit. It cannot resume a completed loop-control path into
the enclosing branch, so the script must receive an ordinary proof refusal,
without attempting to append evidence after the completed `break`. The proof
after the loop is the implicit tail.

```c filename=drain.c
unsigned long drain(unsigned long n) {
    while (n--) { }
    return n;
}
```

```click
target "x86_64-unknown-linux-gnu";
verifying "drain.c";
uint64 drain(uint64 n) {
 requires n <= 15u64;
 ensures result == 18446744073709551615u64;
} by {
 step_until(loop(0).entry);
 loop {
  decreases n;
  invariant n <= 15u64;
  initialize by { close(); }
  maintain by {
   if n == 0u64 { step_until(function.exit); } else { step(); }
  }
 }
}
```

```expect
fail: `step_until` found no checked step from this frontier
```
