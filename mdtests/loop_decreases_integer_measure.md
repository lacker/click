# a loop measure may be a mathematical Integer

The measure is `Integer`-valued, not int32. A counting measure over an array
range is naturally an `Integer` -- an int32 fold's `+` is partial in
specifications, so its bounds are unprovable at a symbolic length -- so the
`decreases` slot takes either carrier. The kernel builds the same two members
it builds for an int32 measure, `0 <= m` and `m_post < m_pre`, over `Integer`
instead: `<` on the nonnegative Integers is well founded for the same reason
`<` on the nonnegative int32s is.

Nothing else moves. The kernel still evaluates the one declared component at
the iteration's entry state and again at the back edge, and the proof still
owes exactly those two members. It states them before the body's step, where
they are ordinary Integer goals, so the closer has them as exact facts; the
bridge from the int32 the C counts to the Integer the measure names is the
prelude's, not the measure's.

```c filename=loop_decreases_integer_measure.c
int32 drain(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "loop_decreases_integer_measure.c";

function level(n: int32) -> Integer {
    to_integer(n)
}

int32 drain(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        decreases level(n);
        invariant 0 <= n;
        initialize by { simp(); }
        preserve by {
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
            close_invariants by { simp(); };
        }
    }
    step();
    simp();
}
```

```expect
pass
```
