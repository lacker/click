# Strict positive-divisor quotient bounds

Truncation toward zero needs a negative lower bound or a positive upper bound.
The bounds remain symbolic and have no native-width assumptions.

```click
import click::integer;

theorem checked_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by {
        have bound * d <= n by { close() using { bound * d < n; }; }
        apply(integer::positive_divisor_quotient_lower(n, d, bound));
        if bound < truncating_quotient(n, d) {
            close();
        } else {
            have truncating_quotient(n, d) == bound by { close() using {
                bound <= truncating_quotient(n, d); not (bound < truncating_quotient(n, d));
            }; }
            if n <= 0 {
                have 0 < d by { close() using { 1 <= d; }; }
                apply(integer::nonpositive_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound, truncating_quotient(n, d));
                    close();
                }
                have not (bound * d < n) by { close() using {
                    n == bound * d + truncating_remainder(n, d); truncating_remainder(n, d) <= 0;
                }; }
                contradiction(bound * d < n);
            } else {
                have 0 <= n by { close() using { not (n <= 0); }; }
                have 0 * d <= n by { close() using { 0 <= n; }; }
                apply(integer::positive_divisor_quotient_lower(n, d, 0));
                have not (bound < 0) by { close() using {
                    0 <= truncating_quotient(n, d); truncating_quotient(n, d) == bound;
                }; }
                contradiction(bound < 0);
            }
        }
    }
}

theorem checked_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by {
        have n <= bound * d by { close() using { n < bound * d; }; }
        apply(integer::positive_divisor_quotient_upper(n, d, bound));
        if truncating_quotient(n, d) < bound {
            close();
        } else {
            have truncating_quotient(n, d) == bound by { close() using {
                truncating_quotient(n, d) <= bound; not (truncating_quotient(n, d) < bound);
            }; }
            if 0 <= n {
                have 0 < d by { close() using { 1 <= d; }; }
                apply(integer::nonnegative_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound, truncating_quotient(n, d));
                    close();
                }
                have not (n < bound * d) by { close() using {
                    n == bound * d + truncating_remainder(n, d); 0 <= truncating_remainder(n, d);
                }; }
                contradiction(n < bound * d);
            } else {
                have n <= 0 by { close() using { not (0 <= n); }; }
                have n <= 0 * d by { close() using { n <= 0; }; }
                apply(integer::positive_divisor_quotient_upper(n, d, 0));
                have not (0 < bound) by { close() using {
                    truncating_quotient(n, d) <= 0; truncating_quotient(n, d) == bound;
                }; }
                contradiction(0 < bound);
            }
        }
    }
}

theorem use_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by apply(integer::positive_divisor_quotient_strict_lower(n, d, bound));
}

theorem use_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by apply(integer::positive_divisor_quotient_strict_upper(n, d, bound));
}

theorem fee_floor_quotient_fit(n: Integer, d: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires -9223372036854775808 * d <= n;
    requires n < 9223372036854775808 * d;
    ensures -9223372036854775808 <= truncating_quotient(n, d) by {
        apply(integer::positive_divisor_quotient_lower(n, d, -9223372036854775808));
    }
    ensures truncating_quotient(n, d) <= 9223372036854775807 by {
        apply(integer::positive_divisor_quotient_strict_upper(n, d, 9223372036854775808));
        close() using { truncating_quotient(n, d) < 9223372036854775808; };
    }
}

theorem fee_ceiling_quotient_fit(n: Integer, d: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires -9223372036854775809 * d < n;
    requires n <= 9223372036854775807 * d;
    ensures -9223372036854775808 <= truncating_quotient(n, d) by {
        apply(integer::positive_divisor_quotient_strict_lower(n, d, -9223372036854775809));
        close() using { -9223372036854775809 < truncating_quotient(n, d); };
    }
    ensures truncating_quotient(n, d) <= 9223372036854775807 by {
        apply(integer::positive_divisor_quotient_upper(n, d, 9223372036854775807));
    }
}

```

```expect
pass
```
