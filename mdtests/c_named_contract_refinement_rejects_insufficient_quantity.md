# Callback refinement rejects an insufficient resource quantity

The target interface supplies `available` credits, but its precondition does
not establish that this covers the `needed` credits required by the source
callback contract.

```click
abstract resource credit();

contract void NeedsCredits(int32 available, int32 needed) {
    requires 0 <= needed;
    owns needed of credit();
}

contract void OffersCredits(int32 available, int32 needed) {
    requires 0 <= available and 0 <= needed;
    owns available of credit();
}

theorem needs_credits_is_offers_credits(
    callback: void (*)(int32, int32)
) {
    requires NeedsCredits(callback);
    ensures OffersCredits(callback) by {
        unfold(NeedsCredits);
        unfold(OffersCredits);
        simp();
    }
}
```

```expect
fail: contract-refinement proof does not establish `OffersCredits(callback)`
```
