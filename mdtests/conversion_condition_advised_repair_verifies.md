# the repair a conversion-condition refusal advises verifies

`conversion_condition_names_the_missing_cell.md` refuses the same theorem and
advises stating the read cell's own loadability as the one-element range
`loadable(p[hi - 1..hi - 1 + 1])`. Advice that has not been run is a guess, so
the advised statement is a fixture of its own.

```click
theorem cell_from_its_own_range(p: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and loadable(p[hi - 1..hi - 1 + 1]);
    ensures to_integer(p[hi - 1]) == to_integer(p[hi - 1]) by { simp(); }
}

theorem overflow_guard_from_its_own_definedness(hi: int32) {
    requires defined(hi - 1);
    ensures to_integer(hi - 1) == to_integer(hi - 1) by { simp(); }
}

theorem conversion_bound_from_its_own_bounds(n: Integer) {
    requires n + 1 >= -2147483648;
    requires n + 1 <= 2147483647;
    ensures to_int32(n + 1) == to_int32(n + 1) by { simp(); }
}
```

```expect
pass
```
