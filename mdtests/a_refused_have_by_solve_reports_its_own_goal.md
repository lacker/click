# A refused have with its proof omitted reports its own goal

A `have ...;` with its proof omitted that the implicit closer cannot prove inside a theorem's
`ensures ... by` block is refused at that `have`, with the `have`'s goal,
not declined to the enclosing claim. The `have` is false: nothing bounds
`word & 1`.

```c filename=a_refused_have_by_solve_reports_its_own_goal.c
void unused(void) {}
```

```click
verifying "a_refused_have_by_solve_reports_its_own_goal.c";

theorem have_goal(word: uint64, base: uint64) {
    requires to_integer(word) == to_integer(base);
    ensures to_integer(word) == to_integer(base) by {
        have (word & 1) == 0;
        close();
    }
}
```

```expect
fail: could not establish `(word & 1) == 0`
```
