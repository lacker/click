# Native buffer offset through a symbolic loop cursor

A loop cursor retains a checked wide offset even when the native spelling
enters through an equality between two offsets in the same external buffer.
The read uses the caller’s view and its explicit native index bound.

```c filename=cursor-one.c
unsigned long f(const unsigned char *input, const unsigned char *buf,
                int narrow, unsigned long native, unsigned n) {
    unsigned long adler = 0;
    do {
        adler += buf[0];
        adler += buf[1];
        buf += 16;
    } while (--n);
    return 0;
}
```

```click
verifying "cursor-one.c";
uint64 f(const uint8* input, const uint8* buf, int32 narrow, uint64 native, uint32 n) {
 requires n == 1u32;
 requires 0 <= narrow;
 requires narrow <= 5536;
 requires native < 5552u64;
 requires native + 1u64 < 5552u64;
 requires input + narrow == input + native;
 requires buf == input + narrow;
 views input[0u64..5552u64];
 ensures result == 0u64;
} by {
 execute_until(loop(0));
 loop {
  decreases to_integer(n);
  invariant n == 1u32;
  invariant buf == input + narrow;
  initialize by simp;
  preserve by { step(); step(); step(); step(); step(); step(); step(); step(); }
 }
 execute(); simp();
}
```

```expect
pass
```
