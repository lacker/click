# a transport does not relate folds over two different arrays

Framing compares the array pointer, it does not prove it equal. A transport
from `zeros(a, 0, n)` at entry to `zeros(b, 0, n)` after a store elsewhere is
refused even though the store touches neither array's fold.

```c filename=fold_read_transport_rejects_a_changed_base_pointer.c
void mark_other(int32 *a, int32 *b, int32 *c, int32 n) {
    c[0] = 1;
}
```

```click
verifying "fold_read_transport_rejects_a_changed_base_pointer.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void mark_other(int32 *a, int32 *b, int32 *c, int32 n) {
    requires 0 < n;
    views a[0..n];
    views b[0..n];
    owns c[0..1];
    ensures zeros(b, 0, n) == old(zeros(a, 0, n));
} by {
    mark entry;
    have zeros(at(entry, a), 0, n) == zeros(at(entry, a), 0, n) by { normalize(); }
    step();
    have zeros(at(entry, a), 0, n) == zeros(b, 0, n) by {
        transport(
            zeros(at(entry, a), 0, n) == zeros(at(entry, a), 0, n),
            zeros(at(entry, a), 0, n) == zeros(b, 0, n)
        ) using {
            zeros(at(entry, a), 0, n) == zeros(at(entry, a), 0, n);
        }
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: fold read frame: the two `zeros` applications differ in an endpoint, a scalar argument or the array pointer
```
