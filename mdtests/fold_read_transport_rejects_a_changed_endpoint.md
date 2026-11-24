# a transport does not relate two applications with different endpoints

The store at `v[i]` misses `ones(v, 0, i)` but the longer application
`ones(v, 0, i + 1)` gains one nonzero element. The stated equality is false:
with `i = 0` and `n = 1`, the old empty fold is zero and the new fold is one.
Neither framing nor unfolding can establish it.

```c filename=fold_read_transport_rejects_a_changed_endpoint.c
void set_end(int32 *v, int32 i, int32 n) {
    v[i] = 1;
}
```

```click
verifying "fold_read_transport_rejects_a_changed_endpoint.c";

function ones(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] != 0 { 1 } else { 0 }) })
}

void set_end(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures ones(v, 0, i + 1) == old(ones(v, 0, i));
} by {
    mark entry;
    have ones(at(entry, v), 0, i) == ones(at(entry, v), 0, i) by close();
    step();
    have ones(at(entry, v), 0, i) == ones(v, 0, i + 1) by {
        close();
        close();
    }
}
```

```expect
fail: `solve` failed
```
