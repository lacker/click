# A condition reaching one truth value along two paths splits into them

A C `if` has one arm per truth value, but its condition can reach one value
along two checked paths: `x > 0 && y > 0` is false when `x > 0` is false and
also when `x > 0` holds and `y > 0` does not.

The implicit tail of `both_positive`'s omitted proof splits on a condition
that every path decides, here `x > 0`, before the `if`, and runs the `if` again in each case. There each
truth value has one path and the C branch applies as usual. Before, the plan
entered the `if` with one path per truth value and dropped the other, and the
checked join refused it: "checked C branch split does not exhaust its
recorded condition paths". The stepped proof writes the same split by hand.

```c filename=a_condition_reaching_one_value_along_two_paths_splits_into_them.c
int32 both_positive(int32 x, int32 y) {
    int32 r;
    if (x > 0 && y > 0) {
        r = 1;
    } else {
        r = 2;
    }
    return r;
}

int32 both_positive_stepped(int32 x, int32 y) {
    int32 r;
    if (x > 0 && y > 0) {
        r = 1;
    } else {
        r = 2;
    }
    return r;
}
```

```click
verifying "a_condition_reaching_one_value_along_two_paths_splits_into_them.c";

int32 both_positive(int32 x, int32 y) {
    ensures result == 2 or (x > 0 and y > 0);
}

int32 both_positive_stepped(int32 x, int32 y) {
    ensures result == 2 or (x > 0 and y > 0);
} by {
    step();
    if x > 0 {
        if y > 0 {
            step();
            step();
            step();
            close();
        } else {
            step();
            step();
            step();
            close();
        }
    } else {
        step();
        step();
        step();
        close();
    }
}
```

```expect
pass
```
