# The library's borrowed C string takes a character pointer

`cstr_at(p, len)` from `click::c::string` has a `const uint8*` parameter, and a
resource argument follows the predicate rule: a `char`, `signed char`, or
`unsigned char` pointer is passed as `uint8` bytes. A signed character
pointer is read through its explicit byte view `src as (uint8 *)`, as
`string::readable(src)` is, so the resource's facts state the string's unsigned
bytes. `measure` lends the borrowed
string to a callee whose parameter has the same character type, and
`copy_prefix` opens it and lends a prefix of its bytes to a `memcpy`-style copy
of `char`.

```c filename=cstr_at_borrows_a_char_string_from_the_library.c
uint64 string_length(const char *s, uint64 n);
uint64 signed_length(const signed char *s, uint64 n);
uint64 unsigned_length(const unsigned char *s, uint64 n);
char *copy_chars(char *destination, const char *source, uint64 bytes);

uint64 measure(const char *src, uint64 n)
{
	return string_length(src, n);
}

uint64 measure_signed(const signed char *src, uint64 n)
{
	return signed_length(src, n);
}

uint64 measure_unsigned(const unsigned char *src, uint64 n)
{
	return unsigned_length(src, n);
}

uint64 copy_prefix(char *dst, const char *src, uint64 n, uint64 k)
{
	copy_chars(dst, src, k);
	return k;
}
```

```click
import click::c::string;

verifying "cstr_at_borrows_a_char_string_from_the_library.c";

extern uint64 string_length(const char* s, uint64 n) {
    views cstr_at(s, n);
    ensures result == n;
}

extern uint64 signed_length(const signed char* s, uint64 n) {
    views cstr_at(s, n);
    ensures result == n;
}

extern uint64 unsigned_length(const unsigned char* s, uint64 n) {
    views cstr_at(s, n);
    ensures result == n;
}

extern char* copy_chars(char* destination, const char* source, uint64 bytes) {
    views source[0..bytes];
    owns destination[0..bytes];
    ensures result == destination;
}

uint64 measure(const char* src, uint64 n) {
    views cstr_at(src, n);
    ensures result == n;
}

uint64 measure_signed(const signed char* src, uint64 n) {
    views cstr_at(src, n);
    ensures result == n;
}

uint64 measure_unsigned(const unsigned char* src, uint64 n) {
    views cstr_at(src, n);
    ensures result == n;
}

uint64 copy_prefix(char* dst, const char* src, uint64 n, uint64 k) {
    views cstr_at(src, n);
    requires k <= n;
    owns dst[0..k];
    ensures result == k;
    ensures (src as (uint8 *))[n] == '\0';
} by {
    open(cstr_at(src, n)) {
    }
}
```

```expect
pass
```
