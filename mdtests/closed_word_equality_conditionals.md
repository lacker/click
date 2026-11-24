# Closed 32-bit equality guards retain their conditional

```click
theorem signed_words(x: int32, y: int32) {
    ensures forall (unused: Integer) {
        (if 1 == 1 { x } else { y }) == x
    } by { intro(); normalize(); }
    ensures forall (unused: Integer) {
        (if 1 != 1 { x } else { y }) == y
    } by { intro(); close(); }
}

theorem unsigned_words() {
    ensures forall (unused: Integer) {
        (if 4294967295u32 == 0u32 { 9u32 } else { 3u32 }) == 3u32
    } by { intro(); close(); }
    ensures forall (unused: Integer) {
        (if 4294967295u32 != 0u32 { 9u32 } else { 3u32 }) == 9u32
    } by { intro(); close(); }
}

theorem dead_arm() {
    ensures (if 9u32 == 8u32 { 1u32 << 32u32 } else { 3u32 }) == 3u32 by close();
    ensures (if 9u32 != 8u32 { 3u32 } else { 1u32 << 32u32 }) == 3u32 by close();
}

theorem pointer_control(p: int32*, q: int32*) {
    ensures (if 9 == 8 { p } else { q }) == q by close();
}
theorem mixed_type_control() {
    ensures (if 1 == 1 { -1 } else { 3u32 }) < 0 by close();
}

theorem bool_control(x: Bool, y: Bool) {
    ensures (if 1 == 1 { x } else { y }) == x by close();
}

```

```expect
pass
```
