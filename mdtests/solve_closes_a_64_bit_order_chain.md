# `solve` closes a 64-bit order chain

`close()` proves an order goal from a chain of `uint64` or `int64` order
facts, as it does for `int32`: the kernel records the facts its 64-bit order
walk used, and `solve` writes them out as the standard library's
transitivity lemmas (`integer::uint64_less_than_less_equal_transitive` and its siblings), each link
stated with `have`. A fact spelled from the other side, `c >= b`, takes part
as `b <= c` does.

`solve_refuses_a_broken_64_bit_order_chain.md` breaks the chain.

```click
import click::integer;

theorem two_links(a: uint64, b: uint64, c: uint64) {
    requires a < b;
    requires b <= c;
    ensures a < c by { close(); }
}
theorem three_links(a: uint64, b: uint64, c: uint64, d: uint64) {
    requires a < b;
    requires b <= c;
    requires c <= d;
    ensures a < d by { close(); }
}
theorem signed_links(a: int64, b: int64, c: int64, d: int64) {
    requires a < b;
    requires c >= b;
    requires c <= d;
    ensures a < d by { close(); }
}
theorem written_from_the_other_side(a: uint64, b: uint64, c: uint64) {
    requires a < b;
    requires c >= b;
    ensures a < c;
}
```

```expect
pass
```
