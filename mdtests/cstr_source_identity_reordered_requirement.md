# Dynamic C-string retry keeps the exact caller requirement identity

The string the call views, `cstr_at(haystack, n)`, is deliberately not the
first entry clause. Unrelated arithmetic, viewability, and resource facts
also ensure that its source ordinal is not its final lowered fact position.

```c filename=cstr_source_identity_reordered_requirement.c
uint64 read_terminator(uint8 haystack[], uint64 known_len) {
    uint64 length;
    length = strlen(haystack);
    return length;
}
```

```click
verifying "cstr_source_identity_reordered_requirement.c";

uint64 read_terminator(uint8 haystack[], uint64 known_len) {
    requires known_len < 18446744073709551615u64;
    requires defined(known_len + 1u64);
    requires viewable(haystack[0..known_len + 1u64]);
    let n: uint64;
    views click::c::string::cstr_at(haystack, n);
    views haystack[0..known_len + 1u64];
    ensures result < 18446744073709551615u64;
}
```

```expect
pass
```
