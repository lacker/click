# Ordinary helper proofs cannot invent a callback guarantee

```click
theorem nonnegative_equal(x: int32, y: int32) {
    requires x >= 0;
    ensures y == x implies y >= 0 by { simp(); }
}

contract int32 Source(int32 x) {
    ensures result == x;
}

contract int32 Target(int32 x) {
    ensures result >= 0;
}

theorem lift(callback: int32 (*)(int32)) {
    requires Source(callback);
    ensures Target(callback) by {
        unfold(Source);
        unfold(Target);
        intro();
        have result == x implies result >= 0 by {
            apply(nonnegative_equal(x, result));
        }
        simp();
    }
}
```

```expect
fail: theorem application `nonnegative_equal` requires an unavailable exact premise
```
