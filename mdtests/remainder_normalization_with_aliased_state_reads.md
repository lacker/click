# Normalize a remainder without rewriting aliased state reads

The read at `before` and the current read denote the same cell value. Rewriting
`p[0] == at(before, p[0]) % divisor` replaces both occurrences in the next
equality, leaving `old(p[0]) % divisor == old(p[0]) % divisor % 65521u32`.
The divisor equality alone does not discharge that extra remainder. Keep the
checked remainder equation and divisor equality selected together instead.
This reduces the state pattern from Adler's four-byte B-lane normalization.

```c filename=probe.c
uint32 observe(uint32 *p, uint32 divisor) { return p[0]; }
```

```click
import click::integer;
verifying "probe.c";
uint32 observe(uint32 *p, uint32 divisor) {
 requires p[0] < divisor;
 requires divisor == 65521u32;
 views p[0];
 ensures result == old(p[0]) % 65521u32;
} by {
 mark before;
 step_until(function.exit);
 have p[0] < divisor;
 apply(integer::uint32_less_than_divisor_implies_remainder_is_value(p[0], divisor)) using { p[0] < divisor; };
 have p[0] == at(before, p[0]) % divisor by solve() using { p[0] % divisor == p[0]; };
 have p[0] == at(before, p[0]) % 65521u32 by {
  solve() using { p[0] == at(before, p[0]) % divisor; divisor == 65521u32; };
 }
 solve();
}
```
```expect
pass
```
