# a library resource needs its module's import

`cstr_at` is declared in `click::c::string`, which is not implicit, and this C
program calls no `<string.h>` function that would bring it. A library
resource is visible exactly when the library's predicates and functions in
its module are, so the contract's resource is unknown and the message names
the import to add. The positive twin is
[`cstr_at_view_passes_through_a_call.md`](cstr_at_view_passes_through_a_call.md).

```c filename=a_library_resource_needs_its_module_import.c
uint64 string_length(const uint8 *s, uint64 n);
```

```click
verifying "a_library_resource_needs_its_module_import.c";

extern uint64 string_length(const uint8* s, uint64 n) {
    views cstr_at(s, n);
    ensures result == n;
}
```

```expect
fail: unknown resource `cstr_at`; it is declared in Click library module `click::c::string`, so add `import click::c::string;`
```
