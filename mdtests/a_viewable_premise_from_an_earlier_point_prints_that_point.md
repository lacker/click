# A viewable premise from an earlier point prints that point

A `viewable` fact is checked in one memory, and an object's lifetime can end
between two points, so a fact from an earlier point is not the fact of the same
range now. The premise list prints it with its point,
`at(function.entry, viewable(...))`: written back, that is the premise the
checker holds. Printed bare, it would look like the current-state fact the
proof wrote, which the checker does not hold.

The proof establishes containment of `p[k..k + 4]` and restricts the view at
entry. After the declaration, `rewrite(q, p + k)` aligns the pointer spelling.
`close()` refuses the current viewability goal and prints the available
window fact at `function.entry`.

```c filename=a_viewable_premise_from_an_earlier_point_prints_that_point.c
unsigned char last(const unsigned char *p, unsigned long n, unsigned long k)
{
	const unsigned char *q = p + k;
	return q[3];
}
```

```click
verifying "a_viewable_premise_from_an_earlier_point_prints_that_point.c";

uint8 last(const uint8* p, uint64 n, uint64 k) {
    requires 4u64 <= n;
    requires k <= n - 4u64;
    requires n <= 4096u64;
    views p[0..n];
    ensures result == p[k + 3u64];
} by {
    have to_integer(k) <= to_integer(k + 4u64);
    have to_integer(k + 4u64) <= to_integer(n);
    have viewable(p[k..k + 4u64]) by {
        have contains(memory(p[0u64..n]), memory(p[k..k + 4u64])) by {
            apply(click::separation::contains_subrange(p, 0u64, n, k, k + 4u64));
        }
        apply(click::separation::viewable_restrict(memory(p[0u64..n]), memory(p[k..k + 4u64])));
    }
    step();
    step();
    have viewable(q[0..4]) by {
        rewrite(q, p + k);
        close();
    }
    step_until(function.exit);
}
```

```expect
fail: at(function.entry, viewable(q[0..k + 4u64 - k]))
```
