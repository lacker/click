# A `Bool` pure function states a claim

A pure function may return `Bool` and take `Bool` parameters. Its body is a
`Bool` value: `true`, `false`, a comparison, `and`, `or`, `not` and
`implies` of `Bool` values, a conditional whose branches are `Bool` values,
or a call of another `Bool` function. A comparison or connective written as
a value is its truth value: `x > 0 and x < 10` is
`if x > 0 { if x < 10 { true } else { false } } else { false }`.

A `Bool` function may recurse on an `int32` measure, as an `int32` one may.

A call of a `Bool` function written where a proposition is expected means
`call == true`, as does a `Bool` parameter written alone, so `ensures
in_range(3);` and `requires flag;` are claims. Predicates are unchanged.

```click
function positive(x: int32) -> Bool { x > 0 }
function in_range(x: int32) -> Bool { x > 0 and x < 10 }
function outside(x: int32) -> Bool { not in_range(x) }
function choose(flag: Bool, x: int32) -> Bool {
    if flag { positive(x) } else { false }
}

function even(n: int32) -> Bool
    decreases n
{
    if n <= 0 { true } else { not even(n - 1) }
}

theorem two_is_even() {
    ensures even(2) by {
        unfold(even(2));
        unfold(even(1));
        unfold(even(0));
        close();
    }
}

theorem three_is_in_range() {
    ensures in_range(3) by {
        unfold(in_range(3));
        close();
    }
}

theorem twelve_is_outside() {
    ensures outside(12) by {
        unfold(outside(12));
        unfold(in_range(12));
        close();
    }
}

theorem chosen_positive(flag: Bool, x: int32) {
    requires flag;
    requires x > 0;
    ensures choose(flag, x) by {
        unfold(choose(flag, x));
        unfold(positive(x));
        close();
    }
}

theorem unchosen(x: int32) {
    ensures choose(false, x) == false by {
        unfold(choose(false, x));
        close();
    }
}
```

```expect
pass
```
