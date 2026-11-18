# strlen of an empty string and memcmp use the catalog contracts

The standard library's libc catalog supplies `strlen` and `memcmp`
contracts without declarations in the sidecar. `strlen` on the empty string
`cstr_at(text, 0u64)` the caller views returns zero through the catalog's
`result == n` postcondition, and `memcmp`
of a viewed two-byte range with itself lends that view as both operands and
discharges its per-byte `defined` precondition from it. This catches a catalog contract whose
precondition or postcondition is not lowered and checked at a call.

```c filename=strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.c
uint64 empty_length(uint8 text[]) {
    uint64 length;
    length = strlen(text);
    return length;
}

int32 compare_self(uint8 bytes[]) {
    return memcmp(bytes, bytes, 2);
}
```

```click
verifying "strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.c";

uint64 empty_length(uint8 text[]) {
    views click::c::string::cstr_at(text, 0u64);
    ensures result == 0u64;
}

int32 compare_self(uint8 bytes[]) {
    views bytes[0..2];
    ensures 1 == 1;
}
```

```expect
pass
```
