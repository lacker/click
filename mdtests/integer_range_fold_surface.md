# Integer range folds retain a scoped mathematical accumulator

```click
function sum_integer_range(lo: Integer, hi: Integer) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + k })
}

function sum_machine_range(n: int32) -> Integer {
    (0..n).fold(0, |acc, k| { acc + to_integer(k) })
}

function sum_machine_range_captured(n: int32, z: Integer) -> Integer {
    (0..n).fold(z, |acc, k| { acc + z + to_integer(k) })
}

theorem integer_range_fold_reflexive(lo: Integer, hi: Integer) {
    ensures sum_integer_range(lo, hi) == sum_integer_range(lo, hi) by {
        normalize();
    }
}

theorem machine_range_reflexive(n: int32) {
    ensures sum_machine_range(n) == sum_machine_range(n) by {
        normalize();
    }
}

theorem machine_range_unfolds(n: int32) {
    ensures sum_machine_range(n) == (0..n).fold(0, |acc, k| { acc + to_integer(k) }) by {
        unfold(sum_machine_range(n));
        normalize();
    }
}

theorem machine_range_captured_unfolds(n: int32, z: Integer) {
    ensures sum_machine_range_captured(n, z) == (0..n).fold(z, |acc, k| { acc + z + to_integer(k) }) by {
        unfold(sum_machine_range_captured(n, z));
        normalize();
    }
}

```

```expect
pass
```
