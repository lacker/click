# apply does not supply a conclusion its theorem lacks

`lower_bound` guarantees `x >= 0` and `x <= 10`. Applying it where `x >= 0` is
the goal keeps both guarantees, and nothing else: `x <= 5` is no conclusion of
the theorem, so the second application still misses its requirement.

```click
predicate small(x: int32) {
    x >= 0 and x <= 10
}

theorem lower_bound(x: int32) {
    requires small(x);

    ensures x >= 0 by {
        unfold(small(x));
        close();
    }

    ensures x <= 10 by {
        unfold(small(x));
        close();
    }
}

theorem needs_tighter_upper(x: int32) {
    requires x <= 5;

    ensures x <= 20 by {
        close();
    }
}

theorem a_missing_conclusion_is_not_invented(x: int32) {
    requires small(x);

    ensures x >= 0 by {
        apply(lower_bound(x));
        apply(needs_tighter_upper(x));
        close();
    }
}
```

```expect
fail: theorem `needs_tighter_upper` has an unproved obligation: `x <= 5`
```
