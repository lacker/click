# a call whose write set starts at the fold's end is framed

`fill` owns `v[lo..n]`, so the call's checked write set is `v[i..n]`. With
`i <= n` that range is well formed and starts exactly where `zeros(v, 0, i)`
ends, so the application survives the call. The rule reads the write set the
call's edge records; it never guesses a callee's footprint.

```c filename=fold_read_transport_across_a_call_with_a_checked_write_set.c
void fill(int32 *v, int32 lo, int32 n) {
    v[lo] = 1;
}

void caller(int32 *v, int32 i, int32 n) {
    fill(v, i, n);
}
```

```click
verifying "fold_read_transport_across_a_call_with_a_checked_write_set.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void fill(int32 *v, int32 lo, int32 n) {
    requires 0 <= lo;
    requires lo < n;
    owns v[lo..n];
} by {
    execute();
    simp();
}

void caller(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures zeros(v, 0, i) == old(zeros(v, 0, i));
} by {
    mark entry;
    have zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i) by { normalize(); }
    have i <= n by { arithmetic() using { i < n; } }
    step();
    have zeros(at(entry, v), 0, i) == zeros(v, 0, i) by {
        transport(
            zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i),
            zeros(at(entry, v), 0, i) == zeros(v, 0, i)
        ) using {
            zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i);
            i <= n;
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
