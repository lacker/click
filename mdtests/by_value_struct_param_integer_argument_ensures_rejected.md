# A by-value struct postcondition is refused when it reads through an Integer argument

The companion of `by_value_struct_param_integer_ensures_rejected.md` where the
read sits inside an Integer argument to a pure function. The parameter-read
check used to skip Integer arguments.

```c filename=integer_argument_ensures.c
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
verifying "integer_argument_ensures.c";

function low(z: Integer) -> int32 {
    if z == 5 { 5 } else { 0 }
}

int32 bump(struct pair value) {
    ensures low(to_integer(value.first)) == 5;
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
