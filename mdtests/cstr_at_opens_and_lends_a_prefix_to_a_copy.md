# A borrowed C string opens and lends a prefix of its bytes

`copy_prefix` borrows the `click::c::string` library resource `cstr_at(src, n)`,
the `n + 1` bytes of `src` through
its terminator with all four facts that make them the C string of length `n`.
It opens the composite and passes the first `k` bytes, for `k <= n`, to a
`memcpy`-style copy whose contract views only `source[0..k]`. The opened view
covers that prefix, and the string's facts are available inside the scope.

```c filename=cstr_at_opens_and_lends_a_prefix_to_a_copy.c
uint8 *copy_bytes(uint8 *destination, const uint8 *source, uint64 bytes);

uint64 copy_prefix(uint8 *dst, const uint8 *src, uint64 n, uint64 k)
{
	copy_bytes(dst, src, k);
	return k;
}
```

```click
import click::c::string;

verifying "cstr_at_opens_and_lends_a_prefix_to_a_copy.c";

extern uint8* copy_bytes(uint8 destination[], const uint8 source[], uint64 bytes) {
    views source[0..bytes];
    owns destination[0..bytes];
    ensures result == destination;
}

uint64 copy_prefix(uint8* dst, const uint8* src, uint64 n, uint64 k) {
    views cstr_at(src, n);
    requires k <= n;
    owns dst[0..k];
    ensures result == k;
    ensures src[n] == '\0';
} by {
    open(cstr_at(src, n)) {
    }
}
```

```expect
pass
```
