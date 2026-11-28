# A closer can discharge the refreshed goal after unfolding

The first `have` proves the concrete color's bit value. In the second
`have`, unfolding `red_bit_value()` exposes the equality already established
by the first proof. Both proofs accept a trailing `close()`.

```c filename=close_after_unfold_refreshes_the_goal.c
int32 red_bit(int32 n) {
    return 0;
}
```

```click
verifying "close_after_unfold_refreshes_the_goal.c";

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
    }
}
```

```expect
pass
```
