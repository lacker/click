# `solve` proves element addresses distinct from their indices

`&q[j] != &q[0]` holds when `j != 0`: the two addresses are the exact scaled
offsets of one base. `solve`'s last strategy reads the goal as two element
addresses of one base with indices of one width and format (`int32`, or
64-bit of one signedness), states the index disequality with `have`, proved
by `solve`, and closes the goal with the library law
`separation::distinct_elements`. `click expand` writes those two steps, as
`explicit` does by hand. The indices are spelled from the index words, so
an `int32` word in arithmetic is `((m - 1) as int32)`.
`mdtests/solve_proves_element_addresses_distinct_at_each_index_type.md`
covers `size_t` and `long` indices and pure theorems.

```c filename=solve_proves_element_addresses_distinct_from_their_indices.c
int last(int *q, int m) { return 0; }
int explicit(int *q, int j) { return 0; }
```

```click
verifying "solve_proves_element_addresses_distinct_from_their_indices.c";

int32 last(int32* q, int32 m) {
    requires 2 <= m and m <= 1000;
    ensures result == 0;
} by {
    have &q[m - 1] != &q[0] by close();
}

int32 explicit(int32* q, int32 j) {
    requires j != 0;
    ensures result == 0;
} by {
    have &q[j] != &q[0] by {
        have j != 0 by { close(); }
        apply(click::separation::distinct_elements(q, j, 0));
    }
}
```

```expect
pass
```
