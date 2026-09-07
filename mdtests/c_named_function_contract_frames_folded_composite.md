# Callback refinement frames folded composites the implementation does not need

The named contract preserves two folded bundles. The concrete callback needs
and returns only the first, so the second remains in the frame around the
concrete transition. Refinement does not inspect either bundle's body.

```c filename=framed_callback_composite.c
int32 keep_first_bundle(int32 key, int32 spare) {
    return key;
}

int32 apply_bundle(
    int32 (*callback)(int32, int32),
    int32 key,
    int32 spare
) {
    return callback(key, spare);
}

int32 framed_bundle_caller(int32 key, int32 spare) {
    return apply_bundle(&keep_first_bundle, key, spare);
}
```

```click
abstract resource permit(key: int32);

resource bundle(key: int32) {
    contains permit(key);
}

verifying "framed_callback_composite.c";

contract int32 PreserveBundles(int32 key, int32 spare) {
    owns bundle(key);
    owns bundle(spare);
    ensures result == key;
}

int32 keep_first_bundle(int32 key, int32 spare) {
    owns bundle(key);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 apply_bundle(
    int32 (*callback)(int32, int32),
    int32 key,
    int32 spare
) {
    requires PreserveBundles(callback);
    owns bundle(key);
    owns bundle(spare);
    ensures result == key;
} by {
    execute();
    simp();
}

int32 framed_bundle_caller(int32 key, int32 spare) {
    owns bundle(key);
    owns bundle(spare);
    ensures result == key;
} by {
    execute();
    simp();
}
```

```expect
pass
```
