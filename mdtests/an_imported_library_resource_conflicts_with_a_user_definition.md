# an imported library resource conflicts with a user definition

The negative twin of
[`an_unimported_library_resource_name_is_free_for_a_user_definition.md`](an_unimported_library_resource_name_is_free_for_a_user_definition.md).
After `import click::c::string;` the library's resource `cstr_at` is visible, so a
user `cstr_at` is a duplicate definition.

```click
import click::c::string;

resource cstr_at(p: const uint8*, len: uint64) {
    views p[0..len + 1u64];
    fact p[len] == '\0';
}
```

```expect
fail: duplicate resource definition `cstr_at`
```
