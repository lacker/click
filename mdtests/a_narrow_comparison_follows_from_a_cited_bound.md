# A narrow comparison follows from a cited bound

An 8-bit comparison is native, so it keeps its own constant's format. The
explicit closers decide it from a cited bound on the same operand as they do
at 32 and 64 bits. The library's `stdio::padded_digit_lower_bound` proof
closes its else arm this way, after the `if` reduces to the digit.

```click
theorem else_arm(b: uint8, x: uint64, y: uint64) {
    requires 48u8 <= b;
    requires not (x < y);
    ensures 48u8 <= (if x < y { 48u8 } else { b }) by {
        solve() using { not (x < y); 48u8 <= b; };
    }
}

theorem strict(b: uint8, x: uint8, y: uint8) {
    requires 48u8 < b;
    requires not (x < y);
    ensures 48u8 < (if x < y { 49u8 } else { b }) by {
        normalize() using { not (x < y); 48u8 < b; };
    }
}

theorem weaker(b: uint8) {
    requires 50u8 <= b;
    ensures 48u8 <= b by { normalize() using { 50u8 <= b; }; }
}
```

```expect
pass
```
