# `bool` negation, disequality and `false` agree

A `bool` value is exactly `false` or `true`, so `not b`, `b != true` and
`b == false` are one claim, as are `b`, `b != false` and `b == true`. No
lemma is needed to move between the spellings, for a `bool` function's
application or a `bool` parameter. The range `b == true or b == false` is a
disjunction, proved like any other by a case split.

```click
function positive(x: int32) -> bool { x > 0 }

theorem not_false_is_true(x: int32) {
    requires positive(x) != false;
    ensures positive(x) by { simp(); }
}

theorem not_is_false(x: int32) {
    requires not positive(x);
    ensures positive(x) == false by { simp(); }
}

theorem not_true_is_not(x: int32) {
    requires positive(x) != true;
    ensures not positive(x) by { simp(); }
}

theorem parameter_not_false_is_true(flag: bool) {
    requires flag != false;
    ensures flag by { simp(); }
}

theorem parameter_not_is_false(flag: bool) {
    requires not flag;
    ensures flag == false by { simp(); }
}

theorem range(x: int32) {
    ensures positive(x) == true or positive(x) == false by {
        if positive(x) {
            assumption();
        } else {
            have positive(x) == false by simp();
            assumption();
        }
    }
}
```

```expect
pass
```
