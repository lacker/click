# A resource fact guard of exact observations bounds its index

Specification arithmetic is over Integer, so a guard that means the C sum
observes it exactly: `to_integer(k) < to_integer(len + 1u64)` is the native
`k < len + 1u64`, and it bounds the fact's read of `p[k]` by the owned
`p[0..len + 1u64]`. This is how `click::c::string`'s `cstr_at` states its
definedness fact. The same guard one element wider is
`resource_fact_guard_of_exact_observations_past_its_range_is_refused.md`.

```click
resource terminated(p: const uint8*, len: uint64) {
    owns p[0..len + 1u64];
    fact len < 18446744073709551615u64;
    fact forall (k: uint64) {
        0u64 <= k and to_integer(k) < to_integer(len + 1u64) implies defined(p[k])
    };
}
```

```expect
pass
```
