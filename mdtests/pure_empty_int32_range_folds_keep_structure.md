# Simple int32 range folds retain their binders and endpoints

```click
theorem literal_empty() {
    ensures forall (unused: Integer) {
        (3..3).fold(5, |acc: int32, k: int32| -> int32 { k }) == 5
    } by { intro(); close(); }
}

theorem symbolic_empty(n: int32) {
    ensures forall (unused: Integer) {
        (n..n).fold(5, |acc: int32, k: int32| -> int32 { k }) == 5
    } by { intro(); close(); }
}

theorem descending_empty() {
    ensures forall (unused: Integer) {
        (3..1).fold(5, |acc: int32, k: int32| -> int32 { k }) == 5
    } by { intro(); close(); }
}

theorem symbolic_seed(n: int32, seed: int32) {
    ensures forall (unused: Integer) {
        (n..n).fold(seed, |acc: int32, k: int32| -> int32 { acc + k }) == seed
    } by { intro(); close(); }
}

theorem signed_order() {
    ensures (1..(-3)).fold(-5, |acc: int32, k: int32| -> int32 { k }) < -4
        by { close(); }
}

theorem observed_empty(n: int32, seed: int32) {
    ensures to_integer((n..n).fold(seed, |acc: int32, k: int32| -> int32 { acc + k })) + 1
        == to_integer(seed) + 1 by { close(); }
}

theorem longer_literal_nonempty() {
    ensures forall (unused: Integer) {
        (1..4).fold(5, |acc: int32, k: int32| -> int32 { k }) == 3
    } by { intro(); close(); }
}

theorem literal_body() {
    ensures forall (unused: Integer) {
        (1..3).fold(5, |acc: int32, k: int32| -> int32 { 7 }) == 7
    } by { intro(); close(); }
}

theorem accumulator_projection(seed: int32) {
    ensures forall (unused: Integer) {
        (1..3).fold(seed, |acc: int32, k: int32| -> int32 { acc }) == seed
    } by { intro(); close(); }
}

theorem accumulator_bound(seed: int32) {
    requires seed < 9;
    ensures (1..3).fold(seed, |acc: int32, k: int32| -> int32 { acc }) < 9
        by { close(); }
}

theorem negative_item() {
    ensures ((-3)..(-1)).fold(5, |acc: int32, k: int32| -> int32 { k }) < -1
        by { close(); }
}

theorem symbolic_control(lo: int32, hi: int32) {
    ensures forall (unused: Integer) {
        (lo..hi).fold(5, |acc: int32, k: int32| -> int32 { k })
            == (lo..hi).fold(5, |acc: int32, k: int32| -> int32 { k })
    } by { intro(); normalize(); }
}
```

```expect
pass
```
