# A pure-function argument converts modulo its parameter type

An argument passed to a pure function's machine-integer parameter is
converted to the parameter type as C converts a call argument, modulo 2^N:
`256` reaches a `uint8` parameter as `0`. The false claim that it arrives as
`256` is refused.

```click
function byte_plus_one(word: uint8) -> int32 { word + 1 }
theorem wraps() {
    ensures byte_plus_one(256) == 1 by {
        unfold(byte_plus_one(256)); normalize();
    }
}
theorem out_of_range() {
    ensures byte_plus_one(256) == 257 by {
        unfold(byte_plus_one(256)); normalize();
    }
}
```

```expect
fail: `out_of_range.ensures_0` proof step tactic 1: `normalize` goal did not normalize to true
```
