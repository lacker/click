# Equal constructor tags do not establish equal fields

```click
spec enum Payload { Value(int32) }
function same_payload(x: int32, y: int32) -> int32 {
    if Payload::Value(x) == Payload::Value(y) { 1 } else { 0 }
}
theorem unequal_fields_are_not_assumed_equal(x: int32, y: int32) {
    ensures same_payload(x, y) == 1 by {
        unfold(same_payload(x, y));
        normalize() using { };
    }
}
```

```expect
fail: `normalize using` goal did not normalize to true using the listed conditions
```
