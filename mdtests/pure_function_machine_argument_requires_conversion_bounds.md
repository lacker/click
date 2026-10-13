# A pure-function argument cannot bypass its parameter's narrowing bounds

```click
function byte_plus_one(word: uint8) -> int32 { word + 1 }
theorem out_of_range() {
    ensures byte_plus_one(256) == 257 by {
        unfold(byte_plus_one(256)); normalize();
    }
}
```

```expect
fail: uint8 narrowing upper bound: 256 <= 255 is false
```
