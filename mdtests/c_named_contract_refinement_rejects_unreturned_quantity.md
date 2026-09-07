# Callback refinement rejects a resource quantity that is not returned

Although the target supplies enough credits to call the source callback, the
source consumes `used` credits. Its output plus the framed remainder therefore
cannot reconstruct the `available` credits promised by the target.

```click
abstract resource credit();

contract void SpendUsed(int32 available, int32 used) {
    requires 0 <= used;
    consumes used of credit();
}

contract void PreserveAvailable(int32 available, int32 used) {
    requires 0 <= used and used <= available;
    owns available of credit();
}

theorem spending_used_preserves_available(
    callback: void (*)(int32, int32)
) {
    requires SpendUsed(callback);
    ensures PreserveAvailable(callback) by {
        unfold(SpendUsed);
        unfold(PreserveAvailable);
        simp();
    }
}
```

```expect
fail: contract-refinement proof does not establish `PreserveAvailable(callback)`
```
