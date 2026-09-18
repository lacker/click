# a C recursion measure may be a mathematical Integer

The function-level `decreases` slot takes the same two carriers the loop slot
takes. `level` returns a mathematical `Integer`, so the measure Click reads at
`drain`'s own entry and again at each call to `drain` inside it is an
`Integer`, and the two members the call owes are built over `Integer`: the
callee's measure is nonnegative, and it is strictly below the entry value.
That is the same argument an int32 measure makes, in the carrier a counting
measure naturally has.

Nothing analyses the body. The descent is an ordinary verification condition at
the recursive `step()`, stated by the proof exactly as a precondition is. The
application is opaque, so each `have` unfolds it, and the prelude's int32-to-
Integer theorems carry the int32 the C counts into the Integer the measure
names.

```c filename=c_decreases_integer_measure_recursion.c
int32 drain(int32 n) {
    int32 result;
    if (n > 0) {
        result = drain(n - 1);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_integer_measure_recursion.c";

function level(n: int32) -> Integer {
    to_integer(n)
}

int32 drain(int32 n) {
    decreases level(n);
    requires n >= 0;
    ensures result == 0;
} by {
    step();
    branch {
        then {
            have 0 <= n - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(n)) using {
                    n > 0;
                }
            }
            have 1 <= n by {
                arithmetic() using {
                    n > 0;
                }
            }
            have defined(n - 1) by {
                apply(int32_nonnegative_subtract_within_value_is_defined(n, 1)) using {
                    1 <= n;
                }
                simp();
            }
            have 0 <= level(n - 1) by {
                unfold(level(n - 1));
                apply(int32_less_equal_to_integer(0, n - 1)) using {
                    0 <= n - 1;
                }
                simp();
            }
            have level(n - 1) < level(n) by {
                unfold(level(n - 1));
                unfold(level(n));
                apply(int32_subtract_to_integer(n, 1)) using {
                    defined(n - 1);
                }
                simp() using {
                    to_integer(n - 1) == to_integer(n) - to_integer(1);
                };
            }
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    simp();
}
```

```expect
pass
```
