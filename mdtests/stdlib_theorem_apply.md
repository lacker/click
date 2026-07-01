# standard-library theorem application

This checks that pure theorem proofs can apply theorem declarations from the
standard library.

```click
theorem user_reuses_cstr_len_has_prefix(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures cstr_prefix(bytes, len) by {
        apply(cstr_len_has_prefix(bytes, len));
        simp();
    }
}
```

```expect
pass
```
