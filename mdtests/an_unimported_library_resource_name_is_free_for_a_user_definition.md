# a resource name in an unimported library module is free for a user definition

`click::c::string` declares the resource `cstr_at`, but this file does not import
it, so its own `cstr_at`, which states no terminator, is the only one it
sees. The negative twin is
[`an_imported_library_resource_conflicts_with_a_user_definition.md`](an_imported_library_resource_conflicts_with_a_user_definition.md).

```c filename=an_unimported_library_resource_name_is_free_for_a_user_definition.c
uint64 string_length(const uint8 *s, uint64 n);

uint64 measure(const uint8 *src, uint64 n)
{
	return string_length(src, n);
}
```

```click
resource cstr_at(p: const uint8*, len: uint64) {
    views p[0..len + 1u64];
    fact len < 18446744073709551615u64;
}

verifying "an_unimported_library_resource_name_is_free_for_a_user_definition.c";

extern uint64 string_length(const uint8* s, uint64 n) {
    views cstr_at(s, n);
    ensures result == n;
}

uint64 measure(const uint8* src, uint64 n) {
    views cstr_at(src, n);
    ensures result == n;
}
```

```expect
pass
```
