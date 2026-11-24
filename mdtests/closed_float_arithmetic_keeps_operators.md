# A closed float predicate keeps its arithmetic

```click
theorem round_once_per_operation() {
    ensures forall (unused: Integer) {
        ((float32_from_bits(0x3f800000u32) + float32_from_bits(0x33800000u32)) as float)
            == float32_from_bits(0x3f800000u32)
    } by { intro(); close(); }
    ensures forall (unused: Integer) {
        ((float64_from_bits(0x3ff0000000000000u64) - float64_from_bits(0x3ff0000000000000u64)) as double)
            == float64_from_bits(0u64)
    } by { intro(); close(); }
}

theorem exceptional_results() {
    ensures forall (unused: Integer) {
        isnan(float32_from_bits(0u32) / float32_from_bits(0u32))
    } by { intro(); close(); }
    ensures forall (unused: Integer) {
        not (((float64_from_bits(0u64) / float64_from_bits(0u64)) as double) <= float64_from_bits(0u64))
    } by { intro(); close(); }
}
```

```expect
pass
```
