# A `bool` pure function states a claim

A pure function may return `bool` and take `bool` parameters. Its body is a
`bool` value: `true`, `false`, a comparison, `and`, `or`, `not` and
`implies` of `bool` values, a conditional whose branches are `bool` values,
or a call of another `bool` function. A comparison or connective written as
a value is its truth value: `x > 0 and x < 10` is
`if x > 0 { if x < 10 { true } else { false } } else { false }`.

A `bool` function may recurse on an `int32` measure, as an `int32` one may.

A call of a `bool` function written where a proposition is expected means
`call == true`, as does a `bool` parameter written alone, so `ensures
in_range(3);` and `requires flag;` are claims. Predicates are unchanged.

```click
function positive(x: int32) -> bool { x > 0 }
function in_range(x: int32) -> bool { x > 0 and x < 10 }
function outside(x: int32) -> bool { not in_range(x) }
function choose(flag: bool, x: int32) -> bool {
    if flag { positive(x) } else { false }
}

function even(n: int32) -> bool
    decreases n
{
    if n <= 0 { true } else { not even(n - 1) }
}

theorem two_is_even() {
    ensures even(2) by {
        unfold(even(2));
        unfold(even(1));
        unfold(even(0));
        normalize();
    }
}

theorem three_is_in_range() {
    ensures in_range(3) by {
        unfold(in_range(3));
        normalize();
    }
}

theorem twelve_is_outside() {
    ensures outside(12) by {
        unfold(outside(12));
        unfold(in_range(12));
        normalize();
    }
}

theorem chosen_positive(flag: bool, x: int32) {
    requires flag;
    requires x > 0;
    ensures choose(flag, x) by {
        unfold(choose(flag, x));
        unfold(positive(x));
        simp();
    }
}

theorem unchosen(x: int32) {
    ensures choose(false, x) == false by {
        unfold(choose(false, x));
        normalize();
    }
}
```

```expect
pass
```
