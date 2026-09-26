# A refused recursion measure spells the measure and the goal it owed

`decreases n ^ -1` is the bitwise complement of `n`, which is negative for
every `n` that reaches the recursive call, so the measure's nonnegativity
obligation there is false and `execute()` refuses the call's prerequisite.

Two parts of that refusal used to print no source. The measure's name in the
obligation was the parsed expression's structural dump,
`BitwiseXor(CFragment(Variable("n")), Negate(IntegerLiteral("1")))`, because
the measure printer had no spelling for a bitwise operator; and the condition
search named only the kind of the goal it could not derive, "did not derive
signed less-or-equal is true". Both now print the measure and the goal as
source.

```c filename=recursion_measure_refusal_spells_its_measure_and_goal.c
int32 count(int32 n) {
    if (n <= 0) {
        return 0;
    }
    return count(n - 1);
}
```

```click
verifying "recursion_measure_refusal_spells_its_measure_and_goal.c";

int32 count(int32 n) {
    decreases n ^ -1;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: `step()` is missing prerequisite (count recursion measure: `(n ^ -1)` is nonnegative at the recursive call): condition-certificate premise search did not derive `0 <= (-1 ^ (n - 1))`
```
