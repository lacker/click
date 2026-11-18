# standard-library theorem application

This checks that pure theorem proofs can apply theorem declarations from the
standard library.

```click
import click::c::string;

theorem user_reuses_cstr_len_has_prefix(bytes: uint8[], len: uint64) {
    requires string::len(bytes, len);

    ensures string::prefix(bytes, len) by {
        apply(string::len_has_prefix(bytes, len));
        solve();
    }
}
```

```expect
pass
```
