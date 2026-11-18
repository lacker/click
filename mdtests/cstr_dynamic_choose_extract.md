# An observed C-string supplies the readable witness

Observe the explicitly named borrowed string after the local declaration.
Its current body facts supply the witness length, terminator, nonzero prefix,
and initialized reads through ordinary instantiation.

```c filename=cstr_dynamic_choose_extract.c
uint64 read_terminator(uint8 bytes[]) {
    uint64 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_choose_extract.c";

uint64 read_terminator(uint8 bytes[]) {
    requires click::c::string::readable(bytes);
    let n: uint64;
    views click::c::string::cstr_at(bytes, n);
    ensures result < 18446744073709551615u64 by {
        step_until(region(1));
        observe(click::c::string::cstr_at(bytes, n));
        have viewable(bytes[0..n + 1u64]) by { observe(bytes[0..n + 1u64]); known(); }
        have forall (k: uint64) { to_integer(k) < to_integer(n + 1u64) implies defined(bytes[k]) } by {
            intro(); intro();
            have 0u64 <= k by { normalize(); }
            instantiate(forall (j: uint64) { 0u64 <= j and to_integer(j) < to_integer(n + 1u64) implies defined(bytes[j]) }, k);
            known();
        }
        have forall (k: uint64) { k < n implies bytes[k] != '\0' } by {
            intro(); intro();
            have 0u64 <= k by { normalize(); }
            instantiate(forall (j: uint64) { 0u64 <= j and j < n implies bytes[j] != '\0' }, k);
            known();
        }
        have exists (len: uint64) {
            len < 18446744073709551615u64 and
                viewable(bytes[0..len + 1u64]) and
                forall (k: uint64) { k < len implies bytes[k] != '\0' } and
                bytes[len] == '\0' and
                forall (k: uint64) { to_integer(k) < to_integer(len + 1u64) implies defined(bytes[k]) }
        } by {
            witness(n);
            known();
        }
    }
}
```

```expect
pass
```
