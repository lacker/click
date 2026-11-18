# A viewed C string cannot be written

`cstr_at(p, len)` owns the `len + 1` bytes of its string, and a contract
chooses how it holds them. `views cstr_at(s, n)` borrows the string read-only:
opening the view exposes the bytes as views, not as owned memory, so `poke`'s
store to the first byte is refused even inside the opened scope. The owning
twin, which rewrites a byte and refolds the string, is
[`cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.md`](cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.md).

```c filename=cstr_at_viewed_string_cannot_be_written.c
void poke(uint8 *s, uint64 n) { s[0] = 'a'; }
```

```click
import click::c::string;

verifying "cstr_at_viewed_string_cannot_be_written.c";

void poke(uint8* s, uint64 n) {
    views cstr_at(s, n);
    requires 0u64 < n;
} by {
    open(cstr_at(s, n)) {
    }
}
```

```expect
fail: could not verify C operation: missing resource fact `owns s[0]`
```
