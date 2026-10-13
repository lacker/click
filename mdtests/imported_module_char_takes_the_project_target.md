# An imported module's `char` takes the importing sidecar's target

A module that declares only definitions has no C target of its own, so its
plain `char` is the importer's. Imported into a user-space sidecar,
`negative_char(c: char)` is about a signed byte and can hold.

```c filename=imported_char_module.c
int is_negative(char c) {
    return c < 0;
}
```

```click
target "x86_64-linux-userspace";
import "userspace_char_predicates_module.click";
verifying "imported_char_module.c";

int32 is_negative(char c) {
    requires negative_char(c);
    ensures result == 1;
} by {
    unfold(negative_char);
    execute();
    simp();
}
```

```expect
pass
```
