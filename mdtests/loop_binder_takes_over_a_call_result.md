# A ranked loop's binder takes over an instance a call renamed

A contracted call that consumes one instance and produces another hands the
caller a resource under a new name. A ranked loop written after it declares its
own binder by family and arguments (D5), so the binder takes over whatever
instance stands at those arguments — here the `chain(n)` the call produced as
`d`, bound in the loop as `c` — and the structural measure `decreases c;` ranks
the loop by it from the first iteration.

The call is `let d = step(touch(n), { c: c });`: the transport names which of
the caller's instances the callee's `consumes` takes, and `d` names what its
`produces` gives back. Nothing in the loop header mentions `d`; the loop finds
the instance at `chain(n)` the way `close_invariants()` finds it at every back
edge.

```c filename=call_before_ranked_loop.c
int32 touch(int32 n) {
    return n;
}

void caller(int32 n) {
    touch(n);
    while (n > 0) {
        n = n - 1;
    }
}
```

```click
verifying "call_before_ranked_loop.c";

spec enum Chain { Nil, Link(Chain) }

resource chain(k: int32) {
    field model: Chain;
    match model {
        Chain::Nil => { fact k == 0; },
        Chain::Link(rest_model) => {
            owns rest: chain(k - 1);
            fact k > 0;
            fact k - 1 >= 0;
            fact rest.model == rest_model;
        },
    }
}

int32 touch(int32 n) {
    requires n >= 0;
    consumes c: chain(n);
    requires c.model != Chain::Nil;
    produces d: chain(n);
    ensures d.model == old(c.model);
} by {
    match c.model {
        Chain::Nil => { contradiction(c.model == Chain::Nil); },
        Chain::Link(rest_model) => {
            unfold(c) as { rest: r };
            let d = fold(chain(n), { model: Chain::Link(rest_model) }, { rest: r });
            have d.model == old(c.model) by { simp(); }
            step();
            simp();
        },
    }
}

void caller(int32 n) {
    requires n >= 0;
    consumes c: chain(n);
    requires c.model != Chain::Nil;
    ensures 1 == 1;
} by {
    let d = step(touch(n), { c: c });
    loop {
        owns c: chain(n);
        decreases c;
        invariant n >= 0;

        initialize by simp;
        preserve by {
            match c.model {
                Chain::Nil => { contradiction(c.model == Chain::Nil); },
                Chain::Link(rest_model) => {
                    unfold(c) as { rest: r };
                    step();
                    close_invariants();
                },
            }
        }
    }
    have n == 0 by { simp(); }
    unfold(c);
    step();
    simp();
}
```

```expect
pass
```
