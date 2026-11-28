# A tactic other than a closer after a closed goal names what closed it

Only a closer may follow a tactic that has discharged a `have` goal.
Here `close()` proves the refreshed goal after unfolding, and the next
`rewrite` reports which tactic closed it.

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
        close();
    }
    have red_bit_value() == 0 by {
        unfold(red_bit_value());
        close();
        rewrite(color_bit(Color::Red), 0);
        close();
    }
}
```

```expect
fail: `close` already closed this goal
```
