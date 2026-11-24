# an Integer loop measure over a model has to stay nonnegative

`chain_len(c.model) - 5` decreases by one with every link the body takes, and
the proof shows that, but an Integer has no least element: a chain shorter than
five links ranks below zero. The bundle keeps its other member, `0 <=` the
measure at the next head, and nothing here proves it, so the back edge is
refused by that member.

```c filename=loop_decreases_model_function_must_stay_nonnegative.c
void countdown(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
}
```

```click
verifying "loop_decreases_model_function_must_stay_nonnegative.c";

spec enum Chain { Nil, Link(Chain) }

function chain_len(m: Chain) -> Integer
    decreases m
{
    match m {
        Chain::Nil => 0,
        Chain::Link(rest) => chain_len(rest) + 1,
    }
}

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

void countdown(int32 n) {
    requires n >= 0;
    consumes c: chain(n);
    ensures 1 == 1;
} by {
    loop {
        owns c: chain(n);
        decreases chain_len(c.model) - 5;
        invariant n >= 0;

        initialize by close();
        maintain by {
            match c.model {
                Chain::Nil => { contradiction(c.model == Chain::Nil); },
                Chain::Link(rest_model) => {
                    have chain_len(c.model) == chain_len(rest_model) + 1 by {
                        rewrite(c.model, Chain::Link(rest_model));
                        unfold(chain_len(Chain::Link(rest_model)));
                        close();
                    }
                    have chain_len(rest_model) - 5 < chain_len(c.model) - 5 by {
                        close() using {
                            chain_len(c.model) == chain_len(rest_model) + 1;
                        };
                    }
                    let { rest: r } = unfold(c);
                    step();
                },
            }
        }
    }
    have n == 0;
    unfold(c);
    step();
    close();
}
```

```expect
fail: the bundle also has `0 <= (chain_len(c.model) - 5)` at the back edge
```
