# Instantiation cannot publish an unguarded conclusion without its guard

```click
function value(z: Integer) -> Integer { z }
theorem missing(x: int32) {
    requires forall (z: Integer) { 0 <= z implies value(z) >= 0 };
    ensures value(to_integer(x)) >= 0 by {
        instantiate(forall (z: Integer) { 0 <= z implies value(z) >= 0 }, to_integer(x));
        known();
    }
}
```

```expect
fail: `known()` could not close the current goal
```
