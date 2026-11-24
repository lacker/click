# A signed index conversion shows in an element address

`p + k` and `p + (k as int64)` for a `uint64` `k` are different addresses
whenever `k` is at least `2^63`: one adds `k`, the other a negative number.
A 64-bit index carries no signedness of its own, so both share the index
`k` and differ only in whether their offset reads it as unsigned. Both
printed `&p[k]`, a goal that read as trivially true and did not close. An
index read with the other signedness than its variable's type shows the
conversion.

```c filename=a_signed_index_conversion_shows_in_an_element_address.c
#include <stddef.h>

const unsigned char *at_offset(const unsigned char *p, size_t k) {
    return p + k;
}
```

```click
verifying "a_signed_index_conversion_shows_in_an_element_address.c";

const uint8* at_offset(const uint8* p, uint64 k) {
    requires k < 4u64;
    views p[0..4];
    ensures result == p + k;
} by {
    have p + k == p + (k as int64) by { close(); }
}
```

```expect
fail: goal: address(&p[k]) == address(&p[k as int64])
```
