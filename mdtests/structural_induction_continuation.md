# A structural match can continue with proof steps

```click
spec enum Chain { Nil, Link(Chain) }
function copy_chain(xs: Chain) -> Chain decreases xs {
    match xs {
        Chain::Nil => Chain::Nil,
        Chain::Link(tail) => Chain::Link(copy_chain(tail)),
    }
}

theorem continuation(xs: Chain) {
    ensures copy_chain(xs) == xs by {
        let ih = induct(xs);
        match xs {
            Chain::Nil => {}
            Chain::Link(tail) => { apply(ih(tail)); }
        }
        have xs == xs by close();
        unfold(copy_chain(xs));
        close();
    }
}
```

```expect
pass
```
