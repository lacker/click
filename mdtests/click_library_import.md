# a Click library module is imported by its `click::` path

The nested path `click::c::string` names `library/c/string.click`.
Repeated imports of a module are accepted. A selective import makes
the named declaration available by its bare name.

```click
import click::c::string;
import click::c::string;
import click::c::string::{len_is_viewable};

theorem imported_cstr_len_is_viewable(bytes: uint8[], len: uint64) {
    requires string::len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        apply(len_is_viewable(bytes, len));
    }
}
```

```expect
pass
```
