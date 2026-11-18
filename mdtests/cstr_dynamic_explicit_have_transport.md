# An observed C-string supplies current readable facts

After the local declaration, observe the held string and its byte range.
Instantiate its current quantified facts to construct the readable witness;
no entry-to-current memory transport is needed.

```c filename=cstr_dynamic_explicit_have_transport.c
int32 read_terminator(uint8 bytes[], uint64 known_len) {
    uint64 length;
    length = strlen(bytes);
    return bytes[length];
}
```

```click
verifying "cstr_dynamic_explicit_have_transport.c";

int32 read_terminator(uint8 bytes[], uint64 known_len) {
    requires click::c::string::readable(bytes);
    requires click::c::string::readable_len(bytes, known_len);
    requires known_len < 18446744073709551615u64;
    requires viewable(bytes[0..known_len + 1u64]);
    views click::c::string::cstr_at(bytes, known_len);
    ensures result == '\0' by {
        step_until(region(1));
        observe(click::c::string::cstr_at(bytes, known_len));
        have viewable(bytes[0..known_len + 1u64]) by { observe(bytes[0..known_len + 1u64]); known(); }
        have forall (k: uint64) { to_integer(k) < to_integer(known_len + 1u64) implies defined(bytes[k]) } by {
            intro(); intro();
            have 0u64 <= k by { normalize(); }
            instantiate(forall (j: uint64) { 0u64 <= j and to_integer(j) < to_integer(known_len + 1u64) implies defined(bytes[j]) }, k);
            known();
        }
        have forall (k: uint64) { k < known_len implies bytes[k] != '\0' } by {
            intro(); intro();
            have 0u64 <= k by { normalize(); }
            instantiate(forall (j: uint64) { 0u64 <= j and j < known_len implies bytes[j] != '\0' }, k);
            known();
        }
        have exists (len: uint64) {
            len < 18446744073709551615u64 and
                viewable(bytes[0..len + 1u64]) and
                forall (k: uint64) { k < len implies bytes[k] != '\0' } and
                bytes[len] == '\0' and
                forall (k: uint64) { to_integer(k) < to_integer(len + 1u64) implies defined(bytes[k]) }
        } by {
            witness(known_len);
            known();
        }
    }
}
```

```expect
pass
```
