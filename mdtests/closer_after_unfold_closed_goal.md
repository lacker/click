# A closer after an `unfold` that already closed the goal is a no-op

`unfold` refreshes the goal through one defining equation, and when the
refreshed goal is already an available fact the goal is closed by that
alone; when it is not, a `normalize()` closes what is left. A proof cannot
always tell which it will be, so a trailing `assumption`, `simp`, or
`normalize` after a closed goal asserts a closed judgment and emits nothing,
in any position. The first `have` below needs its `normalize()`; the second
does not, because unfolding `red_bit_value()` leaves exactly the fact the
first established, and the same script shape is accepted for both.

```c filename=closer_after_unfold_closed_goal.c
int32 red_bit(int32 n) {
    return 0;
}
```

```click
verifying "closer_after_unfold_closed_goal.c";

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
        normalize();
    }
    execute();
    simp();
}
```

```expect
pass
```
