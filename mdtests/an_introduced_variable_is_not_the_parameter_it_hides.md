# An introduced variable is not the parameter it hides

The negative twin of
[`an_introduced_variable_hides_a_parameter_of_its_name.md`](an_introduced_variable_hides_a_parameter_of_its_name.md):
after `intro()`, `y` is the introduced variable, which the requirement on
the parameter `y` says nothing about.

```click
theorem t(y: int32) {
    requires y == 7;
    ensures forall (y: int32) { y == y } by {
        intro();
        have y == 7 by { known(); }
        solve();
    }
}
```

```expect
fail: `known()` could not close the current goal
```
