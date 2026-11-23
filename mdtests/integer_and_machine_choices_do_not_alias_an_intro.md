# Logical choices remain independent of universal witnesses

```click
theorem choices_are_distinct_from_an_arbitrary_machine_value() {
    requires exists (x: Integer) { x == 0 };
    requires exists (y: int32) { y == 0 };
    ensures forall (arbitrary: int32) { arbitrary == 0 } by {
        let integer_choice = obtain(exists (integer_choice: Integer) { integer_choice == 0 });
        intro();
        let machine_choice = obtain(exists (machine_choice: int32) { machine_choice == 0 });
        known();
    }
}
```

```expect
fail: could not close the current goal
```
