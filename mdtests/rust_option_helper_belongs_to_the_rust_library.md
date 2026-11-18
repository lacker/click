# Rust's defaulting helper belongs to the Rust library

The shared `Option` datatype is in scope. The Rust helper has the path
`click::rust::option::unwrap_or`.

```click
theorem shared_option_cannot_name_a_rust_helper(default: int32) {
    ensures click::option::unwrap_or(Option<int32>::None, default) == default;
}
```

```expect
fail: `click::option::unwrap_or` names no declaration of Click library module `click::option`
```
