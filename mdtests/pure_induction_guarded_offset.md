# Numeric induction preserves guarded index expressions

The hypothesis keeps every requirement at its smaller argument. Its guarded
addition uses those premises during lowering and expanded proof reverification.

```click
function guarded_countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { guarded_countdown(n - 1) }
}

theorem guarded_count(base: int32, n: int32) {
    requires 0 <= base;
    requires 0 <= n;
    requires base <= 1000000;
    requires n <= 1000000;
    requires defined(base + n);
    ensures guarded_countdown(n) == 0 and base + n == base + n by {
        let ih = induct(n);
        if n <= 0 {
            all {
                guarded_countdown(n) == 0 => { unfold(guarded_countdown(n)); close() using { n <= 0; }; }
                base + n == base + n => { close(); }
            }
        } else {
            have 0 < n;
            have defined(n - 1);
            have 0 <= to_integer(n - 1);
            have base <= 2147483647 - (n - 1) by { close() using { 0 <= base; base <= 1000000; 0 <= n; n <= 1000000; 0 < n; }; }
            have n - 1 <= 1000000 by { close() using { 0 < n; n <= 1000000; }; }
            have defined(base + (n - 1));
            have defined(base + (n - 1)) by close();
            have to_integer(n - 1) < to_integer(n);
            have to_integer(n - 1) <= 1000000;
            apply(ih(n - 1));
            all {
                guarded_countdown(n) == 0 => {
                    unfold(guarded_countdown(n));
                    rewrite(guarded_countdown(n - 1), 0);
                    close() using { not(n <= 0); };
                }
                base + n == base + n => { close(); }
            }
        }
    }
}
```

```expect
pass
```
