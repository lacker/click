# Function-exit execution refuses a completed loop-control path

The original unsigned guard consumes the old value and decrements on every
test, including the final false test. Its lowering introduces a consumed-value
carrier and a break path. `execute()` searches for function exit. In a written preservation proof, it
cannot resume a completed loop-control path into the enclosing branch. This
script must receive an ordinary proof refusal, without attempting to append
evidence after the completed `break`.

```c filename=drain.c
unsigned long drain(unsigned long n) {
    while (n--) { }
    return n;
}
```

```click
target "x86_64-linux-userspace";
verifying "drain.c";
uint64 drain(uint64 n) {
 requires n <= 15u64;
 ensures result == 18446744073709551615u64;
} by {
 execute_until(loop(0));
 loop {
  decreases n;
  invariant n <= 15u64;
  initialize by { assumption(); }
  preserve by { execute(); simp(); }
 }
 execute(); simp();
}
```

```expect
fail: `execute()` found no checked path from this frontier to function exit
```
