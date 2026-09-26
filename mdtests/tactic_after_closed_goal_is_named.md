# A tactic other than a closer after a closed goal names what closed it

Only `assumption`, `simp`, and `normalize` may follow a tactic that already
closed a `have`'s goal. Here `color_bit(Color::Red) == 0` is established
first, so unfolding `red_bit_value()` in the second body leaves exactly that
fact and closes the goal at once; the `rewrite` after it has no goal to
rewrite, and the refusal names the `unfold` rather than reporting a failed
rewrite.

```c filename=tactic_after_closed_goal_is_named.c
int32 red_bit(int32 n) {
    return 0;
}
```

```click
verifying "tactic_after_closed_goal_is_named.c";

spec enum Color { Red, Black }

function color_bit(color: Color) -> int32 {
    match color {
        Color::Red => 0,
        Color::Black => 1,
    }
}

function red_bit_value() -> int32 {
    color_bit(Color::Red)
}

int32 red_bit(int32 n) {
    ensures result == red_bit_value();
} by {
    have color_bit(Color::Red) == 0 by {
        unfold(color_bit(Color::Red));
        normalize();
    }
    have red_bit_value() == 0 by {
        unfold(red_bit_value());
        rewrite(color_bit(Color::Red) == 0);
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: `unfold` already closed this goal
```
