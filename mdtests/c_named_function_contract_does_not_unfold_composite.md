# Callback refinement does not silently unfold composites

The named contract owns a folded bundle whose body contains `permit(key)`.
Formation still rejects a concrete callback requiring that child directly:
refinement treats the folded bundle as an opaque capability and does not
search or unfold resource definitions.

```c filename=unfolded_callback_composite.c
int32 use_permit(int32 key) {
    return key;
}

int32 apply_bundle(int32 (*callback)(int32), int32 key) {
    return callback(key);
}

int32 unfolded_bundle_caller(int32 key) {
    return apply_bundle(&use_permit, key);
}
```

```click
abstract resource permit(key: int32);

resource bundle(key: int32) {
    contains permit(key);
}

verifying "unfolded_callback_composite.c";

contract int32 UseFoldedBundle(int32 key) {
    owns bundle(key);
    ensures result == key;
}

int32 use_permit(int32 key) {
    owns permit(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 apply_bundle(int32 (*callback)(int32), int32 key) {
    requires UseFoldedBundle(callback);
    owns bundle(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 unfolded_bundle_caller(int32 key) {
    owns bundle(key);
    ensures result == key;
} by {
    execute();
    simp();
}
```

```expect
fail: function `use_permit` does not satisfy named contract `UseFoldedBundle`
```
