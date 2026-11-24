# An unwritten arithmetic goal still needs its premise

The companion of `arithmetic_raises_a_goal_an_unfold_left_unwritten.md`
without the `using` premise relating `chain_size(Chain::Link(at, v, rest))` to
`chain_size(rest)`. The goal does not hold on its own, so `close() using {}` refuses
it.

```c filename=unwritten_goal_unlisted.c
void f(int32 *q) {
    return;
}
```

```click
verifying "unwritten_goal_unlisted.c";
spec enum Chain { Leaf, Link(int32*, int32, Chain) }
function chain_size(c: Chain) -> Integer
    decreases c
{
    match c {
        Chain::Leaf => 0,
        Chain::Link(at, v, rest) => 1 + chain_size(rest),
    }
}
function wrap(at: int32*, v: int32, c: Chain) -> Chain {
    Chain::Link(at, v, c)
}
function weight(c: Chain) -> Integer {
    chain_size(c) + 1
}
resource holder(p: int32*) {
    field model: Chain;
    owns *p;
}
void f(int32* q) {
    owns h: holder(q);
    ensures true;
} by {
    match h.model {
        Chain::Leaf => { step_until(function.exit); },
        Chain::Link(at, v, rest) => {
            have chain_size(Chain::Link(at, v, rest)) == 1 + chain_size(rest) by {
                unfold(chain_size(Chain::Link(at, v, rest)));
                close();
            }
            have weight(wrap(at, v, rest)) == chain_size(rest) + 2 by {
                unfold(wrap(at, v, rest));
                unfold(weight(Chain::Link(at, v, rest)));
                close() using {};
            }
            step_until(function.exit);
        },
    }
}
```

```expect
fail: arithmetic read the current goal as an Integer linear claim, which does not hold on its own
```
