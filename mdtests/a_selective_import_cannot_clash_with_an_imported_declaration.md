# A selective import cannot clash with an imported declaration

Like [`a_selective_import_cannot_clash_with_a_file_declaration.md`](a_selective_import_cannot_clash_with_a_file_declaration.md),
for a declaration of an imported module. Before, the library's `length`
silently replaced the imported module's.

```click
import "a_selective_import_cannot_clash_with_an_imported_declaration_module.click";
import click::list::{length};

theorem t(x: int32) {
    requires x == 3;
    ensures length(x) == 3 by { unfold(length); close(); }
}
```

```expect
fail: `length` is imported from the Click library as `click::list::length` and also declared by an imported module
```
