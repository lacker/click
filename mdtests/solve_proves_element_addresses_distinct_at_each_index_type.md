# `solve` proves element addresses distinct at each index type

Variants of
`mdtests/solve_proves_element_addresses_distinct_from_their_indices.md`. A
`size_t` index beside the literal `0` is compared as `uint64`, and the literal
is spelled `0u64` (`words`, `last64`); a `long` index is compared as `int64`
(`longs`). In a pure theorem the indices are the theorem's parameters.

```c filename=solve_proves_element_addresses_distinct_at_each_index_type.c
#include <stddef.h>

int words(int *q, size_t j) { return 0; }
int longs(int *q, long j) { return 0; }
int last64(long *q, size_t n) { return 0; }
```

```click
verifying "solve_proves_element_addresses_distinct_at_each_index_type.c";

int32 words(int32* q, size_t j) {
    requires 1u64 <= j;
    ensures result == 0;
} by {
    have &q[j] != &q[0] by close();
}

int32 longs(int32* q, int64 j) {
    requires j < 0;
    ensures result == 0;
} by {
    have &q[0] != &q[j] by close();
}

int32 last64(int64* q, size_t n) {
    requires 2u64 <= n and n <= 1000u64;
    ensures result == 0;
} by {
    have &q[n - 1] != &q[0] by close();
}

theorem distinct_words(p: int32*, i: int32, j: int32) {
    requires i < j;
    ensures &p[i] != &p[j] by close();
}

theorem distinct_wide(p: int64*, i: uint64, j: uint64) {
    requires i != j;
    ensures &p[j] != &p[i] by close();
}
```

```expect
pass
```
