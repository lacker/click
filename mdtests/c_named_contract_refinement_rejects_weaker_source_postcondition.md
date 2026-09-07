# Contract-to-contract refinement rejects a weaker source guarantee

An abstract callback carrying `AtLeastInput` may return more than its input.
That does not establish the exact result promised by `Identity`, even though
the function-pointer signatures match.

```click
contract int32 AtLeastInput(int32 input) {
    ensures input <= result;
}

contract int32 Identity(int32 input) {
    ensures result == input;
}

theorem at_least_input_is_identity(
    callback: int32 (*)(int32)
) {
    requires AtLeastInput(callback);
    ensures Identity(callback) by {
        unfold(AtLeastInput);
        unfold(Identity);
        simp();
    }
}
```

```expect
fail: contract-refinement proof does not establish `Identity(callback)`
```
