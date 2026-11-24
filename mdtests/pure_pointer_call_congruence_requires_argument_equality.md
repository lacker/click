# Pointer call congruence requires an argument equality

```click
spec enum Handle { None, Some(int32*) }
function handle_pointer(handle: Handle) -> int32* {
    match handle {
        Handle::None => 0,
        Handle::Some(p) => p,
    }
}
theorem pointer_alias(left: Handle, right: Handle, held: int32*) {
    requires held == handle_pointer(left);
    ensures held == handle_pointer(right) by { close(); }
}
```

```expect
fail: could not establish `held == handle_pointer(right)`
```
