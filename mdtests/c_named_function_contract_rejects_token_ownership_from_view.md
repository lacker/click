# A viewed token cannot supply concrete ownership

The direction matters for abstract resources just as it does for memory.  A
named contract that promises only a view cannot satisfy a concrete callback's
ownership requirement.

```c filename=callback_token_ownership_from_view.c
int32 claims_token(int32 key) {
    return key;
}

int32 apply_token(int32 (*callback)(int32), int32 key) {
    return callback(key);
}

int32 token_ownership_from_view_caller(int32 key) {
    return apply_token(&claims_token, key);
}
```

```click
abstract resource permit(key: int32);

verifying "callback_token_ownership_from_view.c";

contract int32 BorrowToken(int32 key) {
    views permit(key);
    ensures result == key;
}

int32 claims_token(int32 key) {
    owns permit(key);
    ensures result == key;
}

int32 apply_token(int32 (*callback)(int32), int32 key) {
    requires BorrowToken(callback);
    views permit(key);
    ensures result == key;
}

theorem proposed_claims_token_contract() {
    ensures BorrowToken(&claims_token) by {
        unfold(BorrowToken(&claims_token));
        close();
    }
}

int32 token_ownership_from_view_caller(int32 key) {
    views permit(key);
    ensures result == key;
} by {
    apply(proposed_claims_token_contract());
}
```

```expect
fail: contract-refinement proof does not establish `BorrowToken(&claims_token)`
```
