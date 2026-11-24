# split, left and right are known

The three closers `split()`, `left()` and `right()` were one idea, "the goal
follows directly from facts", and are now `close()`. The old names are
refused with the replacement.

```click
theorem old_closer_name(x: int32, y: int32) {
    requires 0 <= x;
    requires y == 3;
    ensures 0 <= x and y == 3 by {
        split();
    }
}
```

```expect
fail: `split()` is now `close()`, which closes a conjunction whose sides are facts and a disjunction with one side a fact
```
