# A callback must preserve a folded composite its named contract preserves

Both interfaces can receive the bundle, but the concrete callback consumes it
instead of returning it. It therefore cannot implement a contract that
promises composite ownership back to the caller.

```c filename=consumed_callback_composite.c
int32 consume_bundle(int32 key) {
    return key;
}

int32 apply_bundle(int32 (*callback)(int32), int32 key) {
    return callback(key);
}

int32 consumed_bundle_caller(int32 key) {
    return apply_bundle(&consume_bundle, key);
}
```

```click
abstract resource permit(key: int32);

resource bundle(key: int32) {
    owns permit(key);
}

verifying "consumed_callback_composite.c";

contract int32 PreserveBundle(int32 key) {
    owns bundle(key);
    ensures result == key;
}

int32 consume_bundle(int32 key) {
    consumes bundle(key);
    ensures result == key;
}

int32 apply_bundle(int32 (*callback)(int32), int32 key) {
    requires PreserveBundle(callback);
    owns bundle(key);
    ensures result == key;
}

theorem proposed_consume_bundle_contract() {
    ensures PreserveBundle(&consume_bundle) by {
        unfold(PreserveBundle(&consume_bundle));
        close();
    }
}

int32 consumed_bundle_caller(int32 key) {
    owns bundle(key);
    ensures result == key;
} by {
    apply(proposed_consume_bundle_contract());
}
```

```expect
fail: contract-refinement proof does not establish `PreserveBundle(&consume_bundle)`
```
