# The closer can unfold a function and close its refreshed goal

Unfolding the call refreshes the goal to `1 == 1`. The closer uses the
already available fact to finish the proof.

```click
spec enum Color { Red, Black }

function color_bit(color: Color) -> int {
    match color {
        Color::Red => 0,
        Color::Black => 1,
    }
}

theorem bit_after_a_trivial_have() {
    ensures color_bit(Color::Black) == 1 by {
        have 1 == 1;
        have color_bit(Color::Black) == 1 by close();
        close();
    }
}
```

```expect
pass
```
