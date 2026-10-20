# Integer casts keep historical values

Integer casts convert the value selected by their operand. Observations at
function entry and at a recorded mark keep their own values after execution.

```c filename=historical_cast.c
int bump(int x) {
    x = x + 1;
    return x;
}
```

```click
verifying "historical_cast.c";
int32 bump(int32 x) {
    requires 0 <= x;
    requires x <= 100;
    ensures result == old(x) + 1;
} by {
    mark before;
    step();
    mark after;
    execute();
    have ((int32)old(x)) == at(before, x) by normalize();
    have ((int64)at(before, x)) == old((int64)x) by normalize();
    have ((int32)(at(after, x) - at(before, x))) == 1 by normalize();
    simp();
}
```

```expect
pass
```
