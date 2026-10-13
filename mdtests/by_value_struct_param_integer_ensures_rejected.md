# A by-value struct postcondition is refused when it reads through Integer

The Integer form of `by_value_struct_param_ensures_rejected.md`. `bump`
modifies its private copy of `value`, so a postcondition that reads
`value.first` would describe that copy to the caller. The source check that
refuses such a postcondition skipped Integer comparisons and Integer
arguments, so `to_integer(value.first) == 5` passed it and failed later as an
unexplained unproved goal.

```c filename=integer_ensures.c
struct pair {
    int32 first;
    int32 second;
};

int32 bump(struct pair value) {
    value.first = 5;
    return value.first;
}

int32 call_bump() {
    struct pair original;
    int32 r;
    original.first = 4;
    original.second = 0;
    r = bump(original);
    return original.first;
}
```

```click
verifying "integer_ensures.c";

int32 bump(struct pair value) {
    ensures to_integer(value.first) == 5;
} by {
    execute();
    simp();
}

int32 call_bump() {
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: by-value aggregate parameter `value` is modified, but a postcondition reads its current state
```
