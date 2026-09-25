# a store through a separated array misses the fold

`a` and `b` are two `int32*` parameters, so they share the external-argument
object and no offset relates them. The stated `separate(...)` holds them
apart; the frame rule checks that the fold's cells lie inside its first range
and the written cell inside its second, from exact order facts.

```c filename=fold_read_transport_through_a_separated_alias.c
void mark_other(int32 *a, int32 *b, int32 j, int32 n) {
    b[j] = 1;
}
```

```click
verifying "fold_read_transport_through_a_separated_alias.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void mark_other(int32 *a, int32 *b, int32 j, int32 n) {
    requires 0 <= j;
    requires j < n;
    views a[0..n];
    owns b[0..n];
    requires separate(memory(a[0..n]), memory(b[0..n]));
    ensures zeros(a, 0, n) == old(zeros(a, 0, n));
} by {
    mark entry;
    have zeros(at(entry, a), 0, n) == zeros(at(entry, a), 0, n) by { normalize(); }
    step();
    have zeros(at(entry, a), 0, n) == zeros(a, 0, n) by {
        transport(
            zeros(at(entry, a), 0, n) == zeros(at(entry, a), 0, n),
            zeros(at(entry, a), 0, n) == zeros(a, 0, n)
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
pass
```
