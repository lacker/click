# `simp` closes a goal its unfold already closed

`simp` evaluates `color_bit(Color::Black)` by trying a checked `unfold` of
the call. Unfolding refreshes the goal to `1 == 1`, which lowers to `true`.
After `have 1 == 1;`, `true` is an available fact, so the unfold step closes
the goal by itself. `simp` once kept searching for a closer of a goal that
no longer existed, and reported that it could not establish
`color_bit(Color::Black) == 1`. The same happened in the red-black tree
erase proofs, where earlier steps had made `true` available.

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
        have color_bit(Color::Black) == 1 by simp;
        assumption();
    }
}
```

```expect
pass
```
