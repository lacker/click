# a theorem states a readable range with `views`

A pure theorem has no resource context: nothing is lent to it, nothing is
consumed, and applying it separates nothing. Readability is the one thing a
range still means without an owner, so `views v[lo..hi];` in a theorem is a
hypothesis — reads of that range are defined — and nothing more. It lowers to
the proposition `viewable(v[lo..hi])` states, and carries the same valid-extent
guards, which the proof below assumes and any application owes.

The first theorem reads `v[k]` in its own statement. `to_integer(v[k])` denotes
a value only where that cell is viewable, and the cell comes from the stated
range narrowed by the two order facts, so the `views` clause is load-bearing:
`mdtests/conversion_condition_names_the_missing_cell.md` is the refusal when a
theorem states no range at all.

The second theorem writes the same premise as a bare `requires viewable(...)`.
Both spellings normalize to one premise, so a theorem cannot mean two things by
the same range, and a reader who has not moved to `views` yet keeps a form that
works.

The third applies the first. A `using` list holds propositions, so the `views`
premise is named there by its fact form, `viewable(v[0..hi])`, and the two
valid-extent facts the range carries are named beside it — this theorem's own
`views` clause is where they come from.

```click
theorem cell_of_a_viewed_range(v: int32[], lo: int32, hi: int32, k: int32) {
    views v[lo..hi];
    requires lo <= k;
    requires k < hi;
    ensures to_integer(v[k]) == to_integer(v[k]) by { simp(); }
}

theorem cell_of_a_stated_range(v: int32[], lo: int32, hi: int32, k: int32) {
    requires viewable(v[lo..hi]);
    requires lo <= k;
    requires k < hi;
    ensures to_integer(v[k]) == to_integer(v[k]) by { simp(); }
}

theorem first_cell_of_a_viewed_range(v: int32[], hi: int32) {
    views v[0..hi];
    requires 0 < hi;
    ensures to_integer(v[0]) == to_integer(v[0]) by {
        have 0 <= 0 by { simp(); }
        apply(cell_of_a_viewed_range(v, 0, hi, 0)) using {
            viewable(v[0..hi]);
            0 <= 0;
            0 < hi;
            0 <= hi;
            hi <= 1073741823;
        }
        assumption();
    }
}
```

```expect
pass
```
