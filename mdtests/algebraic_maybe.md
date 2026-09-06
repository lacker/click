# generic nonrecursive algebraic datatypes

This first algebraic-datatype slice defines a generic `Maybe<T>`, constructs
both variants, compares constructed values structurally, and eliminates them
with exhaustive pattern matching. Constructor fields may contain symbolic C
values even though the outer algebraic value is syntactically constructed.

```c filename=algebraic_maybe.c
int32 identity(int32 value) {
    return value;
}
```

```click
verifying "algebraic_maybe.c";

spec enum Maybe<T> {
    None,
    Some(T),
}

predicate wrapped_equal(left: int32, right: int32) {
    Maybe<int32>::Some(left) == Maybe<int32>::Some(right)
}

function unwrap_constructed(value: int32, fallback: int32) -> int32 {
    match Maybe<int32>::Some(value) {
        Maybe::None => fallback,
        Maybe::Some(inner) => inner,
    }
}

theorem maybe_some_reflexive(value: int32) {
    ensures Maybe<int32>::Some(value) == Maybe<int32>::Some(value) by simp;
}

theorem maybe_variants_are_distinct(value: int32) {
    ensures Maybe<int32>::None != Maybe<int32>::Some(value) by simp;
}

theorem maybe_payloads_compare_structurally() {
    ensures Maybe<int32>::Some(0) != Maybe<int32>::Some(1) by simp;
}

theorem maybe_accepts_pointer_type_arguments(value: int32*) {
    ensures Maybe<int32*>::Some(value) == Maybe<int32*>::Some(value) by simp;
}

theorem maybe_works_through_predicates(value: int32) {
    ensures wrapped_equal(value, value) by {
        unfold(wrapped_equal);
        simp();
    }
}

theorem maybe_works_in_pure_functions(value: int32, fallback: int32) {
    ensures unwrap_constructed(value, fallback) == value by simp;
}

theorem maybe_match_some(value: int32, fallback: int32) {
    ensures match Maybe<int32>::Some(value) {
        Maybe::None => fallback,
        Maybe::Some(inner) => inner,
    } == value by simp;
}

theorem maybe_match_none(value: int32, fallback: int32) {
    ensures match Maybe<int32>::None {
        Maybe::None => fallback,
        Maybe::Some(inner) => inner,
    } == fallback by simp;
}

int32 identity(int32 value) {
    ensures result == unwrap_constructed(value, 0) by auto;
}
```

```expect
pass
```
