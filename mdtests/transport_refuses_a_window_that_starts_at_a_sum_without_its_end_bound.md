# A range theorem requires the window end to be inside the view

Narrowing `p[0..n]` to `p[k + 3u64..k + 4u64]` requires the window's end
to be inside the view. Knowing that its start is inside the view leaves
that requirement open.

```c filename=transport_refuses_a_window_that_starts_at_a_sum_without_its_end_bound.c
unsigned char first(const unsigned char *p, unsigned long n, unsigned long k)
{
	return p[0];
}
```

```click
verifying "transport_refuses_a_window_that_starts_at_a_sum_without_its_end_bound.c";

uint8 first(const uint8* p, uint64 n, uint64 k) {
    requires 4u64 <= n;
    requires k <= n - 3u64;
    requires n <= 4096u64;
    views p[0..n];
    ensures result == p[0];
} by {
    have 0 <= to_integer(k + 3u64);
    have to_integer(k + 3u64) <= to_integer(k + 4u64);
    have viewable(p[k + 3u64..k + 4u64]) by {
        have contains(memory(p[0u64..n]), memory(p[k + 3u64..k + 4u64])) by {
            apply(click::separation::contains_subrange(p, 0u64, n, k + 3u64, k + 4u64));
        }
    }
    step_until(function.exit);
    close();
}
```

```expect
fail: has an unproved obligation
```
