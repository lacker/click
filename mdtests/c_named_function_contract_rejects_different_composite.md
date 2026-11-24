# A callback may not require a differently parameterized folded composite

Folded composite identity includes its arguments. Ownership of `bundle(key)`
cannot satisfy a concrete callback requirement for `bundle(other)`.

```c filename=different_callback_composite.c
int32 use_other_bundle(int32 key, int32 other) {
    return key;
}

int32 apply_bundle(
    int32 (*callback)(int32, int32),
    int32 key,
    int32 other
) {
    return callback(key, other);
}

int32 different_bundle_caller(int32 key, int32 other) {
    return apply_bundle(&use_other_bundle, key, other);
}
```

```click
abstract resource permit(key: int32);

resource bundle(key: int32) {
    owns permit(key);
}

verifying "different_callback_composite.c";

contract int32 UseBundle(int32 key, int32 other) {
    owns bundle(key);
    ensures result == key;
}

int32 use_other_bundle(int32 key, int32 other) {
    owns bundle(other);
    ensures result == key;
}

int32 apply_bundle(
    int32 (*callback)(int32, int32),
    int32 key,
    int32 other
) {
    requires UseBundle(callback);
    owns bundle(key);
    ensures result == key;
}

theorem proposed_use_other_bundle_contract() {
    ensures UseBundle(&use_other_bundle) by {
        unfold(UseBundle(&use_other_bundle));
        close();
    }
}

int32 different_bundle_caller(int32 key, int32 other) {
    owns bundle(key);
    ensures result == key;
} by {
    apply(proposed_use_other_bundle_contract());
}
```

```expect
fail: contract-refinement proof does not establish `UseBundle(&use_other_bundle)`
```
