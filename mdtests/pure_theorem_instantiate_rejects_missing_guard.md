# pure theorem instantiate requires guard evidence

The ordinary `have` for the instantiated guard must still fail when its bound
is unavailable. Instantiation never assumes that bound.

```click
theorem bounded_value(value: int32, limit: int32) {
    requires forall (k: int32) {
        0 <= k and k < limit implies k <= value
    };

    ensures 2 <= value by {
        have 0 <= 2 and 2 < limit;
        instantiate(forall (k: int32) {
            0 <= k and k < limit implies k <= value
        }, 2);
        close();
    }
}
```

```expect
fail: could not establish `0 <= 2 and 2 < limit`
```
