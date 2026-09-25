# a fold whose endpoint is a historical read keeps that endpoint

The prefix ends at `m[0]` as read at entry. That argument is an evaluated
value, not an instruction to reload `m[0]` later, so both applications spell
the same endpoint `at(entry, m[0])`. The store writes `v[m[0]]` through the
same load, which is exactly the prefix's end.

```c filename=fold_read_transport_historical_endpoint.c
void mark_at(int32 *v, int32 *m, int32 n) {
    v[m[0]] = 1;
}
```

```click
verifying "fold_read_transport_historical_endpoint.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void mark_at(int32 *v, int32 *m, int32 n) {
    requires 0 <= m[0];
    requires m[0] < n;
    views m[0..1];
    owns v[0..n];
    requires separate(memory(v[0..n]), memory(m[0..1]));
} by {
    mark entry;
    have zeros(at(entry, v), 0, at(entry, m[0])) == zeros(at(entry, v), 0, at(entry, m[0])) by { normalize(); }
    step();
    have zeros(at(entry, v), 0, at(entry, m[0])) == zeros(v, 0, at(entry, m[0])) by {
        transport(
            zeros(at(entry, v), 0, at(entry, m[0])) == zeros(at(entry, v), 0, at(entry, m[0])),
            zeros(at(entry, v), 0, at(entry, m[0])) == zeros(v, 0, at(entry, m[0]))
        ) using {
            zeros(at(entry, v), 0, at(entry, m[0])) == zeros(at(entry, v), 0, at(entry, m[0]));
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
