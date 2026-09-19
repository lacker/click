# arithmetic reads the goal `unfold ... using` refreshed

`unfold(f(args)) using { ... }` refreshes the goal through the range-fold law
the listed guards select. It installs that refreshed claim in both forms: the
kernel proposition the law substituted into, and the written spelling the law
replaced `f(args)` by. A later tactic that dispatches on the written goal --
`arithmetic` over the `Integer` linear fragment among them -- therefore reads
the claim this step left open, not the one the reader wrote before it.

Without the written form, the identical `arithmetic() using` that proves this
claim as a `have` was refused with the signed-int32 planner's precondition,
because the `Integer` route is reached from the written goal.

```click
function total(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

theorem refreshed_goal(lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi < 2147483647;
    requires defined(hi - 1);
    requires lo <= hi - 1;
    ensures total(lo, hi) == total(lo, hi - 1) + to_integer(hi - 1) by {
        have hi - 1 < 2147483647 by {
            arithmetic() using { 0 <= lo; lo < hi; hi < 2147483647; }
        }
        unfold(total(lo, hi)) using {
            lo <= hi - 1;
            hi - 1 < 2147483647;
        }
        arithmetic() using { lo <= hi - 1; }
    }
}
```

```expect
pass
```
