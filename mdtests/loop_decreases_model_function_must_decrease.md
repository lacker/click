# a loop measure over a model still has to decrease

The measure `chain_len(c.model)` is a function of the loop binder's model,
and the body never moves the binder: it spins while `n` is positive and hands
back the instance it started with. The back edge compares the measure against
itself, so the ranking member stays open. A model measure buys no leniency
over a C one; its obligation is the same strict decrease.

```c filename=loop_decreases_model_function_must_decrease.c
void spin(int32 n) {
    while (n > 0) {
    }
}
```

```click
verifying "loop_decreases_model_function_must_decrease.c";

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

void spin(int32 n) {
    requires n >= 0;
    consumes c: chain(n);
    ensures 1 == 1;
} by {
    loop {
        owns c: chain(n);
        decreases chain_len(c.model);
        invariant n >= 0;

        initialize by close();
        maintain by {
            step();
        }
    }
    have n == 0;
    unfold(c);
    step();
    close();
}
```

```expect
fail: `chain_len(c.model)` decreases at the back edge
```
