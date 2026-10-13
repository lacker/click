# `auto` proves a machine conservation equation

`capacity - amount == used + (available - amount)` over `int32` is proved
through its `Integer` reading: the equality fact `capacity == used +
available` is carried to `Integer`, each operation is shown defined and
observed term by term, both bounds of the `Integer` equality are refuted, and
`int32_to_integer_equal_implies_equal` carries it back. The conjunction goal
is split and each side proved the same way.

```click
theorem shrink_conservation(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= amount;
    requires amount <= available;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity - amount);
    ensures capacity - amount == used + (available - amount) by auto;
}

theorem grow_conservation(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= available;
    requires 0 <= amount;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity + amount);
    ensures defined(used + (available + amount)) and
        capacity + amount == used + (available + amount) by auto;
}
```

```expect
pass
```
