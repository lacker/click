# `solve` does not prove element addresses distinct when the indices may be equal

`0 <= j` admits `j == 0`, where `&q[j]` is `&q[0]`. `solve`'s element-address
strategy states `j != 0` and its nested `solve` misses, so the strategy
declines and `solve` reports its ordinary bounded miss.

```c filename=solve_does_not_prove_element_addresses_distinct_when_the_indices_may_be_equal.c
int may_equal(int *q, int j) { return 0; }
```

```click
verifying "solve_does_not_prove_element_addresses_distinct_when_the_indices_may_be_equal.c";

int32 may_equal(int32* q, int32 j) {
    requires 0 <= j;
    ensures result == 0;
} by {
    have &q[j] != &q[0] by close();
}
```

```expect
fail: could not establish `&q[j] != &q[0]`
```
