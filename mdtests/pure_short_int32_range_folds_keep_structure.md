# Short int32 range folds retain their bounds, seed and callback

```click
theorem short_fold_seed(seed: int32) {
    ensures forall (unused: Integer) {
        (1..2).fold(seed, |acc: int32, k: int32| -> int32 { acc }) == seed
    } by { intro(); close(); }
}

theorem short_fold_sum() {
    ensures forall (unused: Integer) {
        (1..3).fold(5, |acc: int32, k: int32| -> int32 { acc + k }) == 8
    } by { intro(); close(); }
}

theorem short_fold_in_arithmetic() {
    ensures to_integer((1..3).fold(5, |acc: int32, k: int32| -> int32 { acc + k }) + 1) == 9
        by { normalize(); }
}

theorem short_fold_with_symbolic_arithmetic(seed: int32) {
    requires seed < 2147483647;
    ensures to_integer((1..2).fold(seed, |acc: int32, k: int32| -> int32 { acc + k }))
        == to_integer(seed + 1) by { normalize(); }
}

theorem short_fold_below_zero() {
    ensures (-2..0).fold(5, |acc: int32, k: int32| -> int32 { acc + k }) == 2
        by { close(); }
}
```

```expect
pass
```
