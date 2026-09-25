# explicit transport states a fold application's value across a store

`zeros(v, 0, i)` reads only the cells below `i`, and the kernel checks that
from its body. The store writes `v[i]`, the first cell past that range, so the
application at the entry snapshot equals the application after the store.
The proof states that equality in surface syntax, as a transport of the
reflexive equation at entry, and the contract's `old(...)` claim follows from
it.

```c filename=fold_read_transport_restates_the_application_equality.c
void set_end(int32 *v, int32 i, int32 n) {
    v[i] = 1;
}
```

```click
verifying "fold_read_transport_restates_the_application_equality.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void set_end(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures zeros(v, 0, i) == old(zeros(v, 0, i));
} by {
    mark entry;
    have zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i) by { normalize(); }
    step();
    have zeros(at(entry, v), 0, i) == zeros(v, 0, i) by {
        transport(
            zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i),
            zeros(at(entry, v), 0, i) == zeros(v, 0, i)
        ) using {
            zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i);
        }
        assumption();
    }
    execute();
    simp();
}
```

```expect
pass
```
