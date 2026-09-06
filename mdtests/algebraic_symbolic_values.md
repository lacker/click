# symbolic algebraic values

Algebraic datatypes are first-class Click types: a pure theorem can quantify
over an arbitrary value, compare it structurally, and eliminate it with an
exhaustive match. This fixture deliberately contains no C program.

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

function wrap(value: int32) -> Maybe<int32> {
    Maybe<int32>::Some(value)
}

function value_or(m: Maybe<int32>, fallback: int32) -> int32 {
    match m {
        Maybe::None => fallback,
        Maybe::Some(value) => value,
    }
}

function rebuild(m: Maybe<int32>) -> Maybe<int32> {
    match m {
        Maybe::None => Maybe<int32>::None,
        Maybe::Some(value) => Maybe<int32>::Some(value),
    }
}

predicate same_maybe(left: Maybe<int32>, right: Maybe<int32>) {
    left == right
}

theorem maybe_reflexive(m: Maybe<int32>) {
    ensures m == m by simp;
}

theorem maybe_match_is_total(m: Maybe<int32>) {
    ensures match m {
        Maybe::None => 0,
        Maybe::Some(value) => value,
    } == match m {
        Maybe::None => 0,
        Maybe::Some(value) => value,
    } by simp;
}

theorem maybe_match_rebuilds(m: Maybe<int32>) {
    ensures match m {
        Maybe::None => Maybe<int32>::None,
        Maybe::Some(value) => Maybe<int32>::Some(value),
    } == m by simp;
}

theorem algebraic_function_result(value: int32) {
    ensures wrap(value) == Maybe<int32>::Some(value) by {
        unfold(wrap(value));
        simp();
    }
    ensures wrap(value) == wrap(value) by simp;
}

theorem algebraic_function_parameter(m: Maybe<int32>, fallback: int32) {
    ensures value_or(m, fallback) == value_or(m, fallback) by simp;
    ensures rebuild(m) == m by {
        unfold(rebuild(m));
        simp();
    }
}

theorem algebraic_predicate_parameter(m: Maybe<int32>) {
    ensures same_maybe(m, m) by simp;
}

theorem algebraic_identity_is_stable(left: Maybe<int32>, right: Maybe<int32>) {
    requires left == right;
    ensures left == right by {
        assumption();
    }
}

theorem maybe_constructor_congruence(left: int32, right: int32) {
    requires left == right;
    ensures Maybe<int32>::Some(left) == Maybe<int32>::Some(right) by simp;
}

theorem maybe_constructor_injectivity(left: int32, right: int32) {
    requires Maybe<int32>::Some(left) == Maybe<int32>::Some(right);
    ensures left == right by simp;
}

theorem maybe_pointer_constructor_rules(left: int32*, right: int32*) {
    requires left == right;
    ensures Maybe<int32*>::Some(left) == Maybe<int32*>::Some(right) by simp;
}

theorem maybe_pointer_constructor_injectivity(left: int32*, right: int32*) {
    requires Maybe<int32*>::Some(left) == Maybe<int32*>::Some(right);
    ensures left == right by simp;
}

theorem maybe_constructor_disjointness_is_checked(value: int32) {
    requires Maybe<int32>::None == Maybe<int32>::Some(value);
    ensures 0 == 1 by simp;
}
```

```expect
pass
```
