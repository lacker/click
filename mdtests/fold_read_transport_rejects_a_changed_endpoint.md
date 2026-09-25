# a transport does not relate two applications with different endpoints

The store at `v[i]` misses `zeros(v, 0, i)` but not `zeros(v, 0, i + 1)`. A
transport from the shorter application to the longer one differs in an
endpoint, which framing alone never equates.

```c filename=fold_read_transport_rejects_a_changed_endpoint.c
void set_end(int32 *v, int32 i, int32 n) {
    v[i] = 1;
}
```

```click
verifying "fold_read_transport_rejects_a_changed_endpoint.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void set_end(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures zeros(v, 0, i + 1) == old(zeros(v, 0, i));
} by {
    mark entry;
    have zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i) by { normalize(); }
    step();
    have zeros(at(entry, v), 0, i) == zeros(v, 0, i + 1) by {
        transport(
            zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i),
            zeros(at(entry, v), 0, i) == zeros(v, 0, i + 1)
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
fail: fold read frame: the two `zeros` applications differ in an endpoint, a scalar argument or the array pointer
```
