# a loop measure over a model may not also read a C local

A measure that reads a binder's model is ranked by the models alone: its two
readings are the head binders' models and the rebound ones. `chain_len(c.model)
+ to_integer(n)` also reads the C local `n`, which moves independently of the
binder, so the measure is refused before any back edge, naming the local.

```c filename=loop_decreases_model_function_rejects_a_c_local.c
void countdown(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
}
```

```click
verifying "loop_decreases_model_function_rejects_a_c_local.c";

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
        decreases chain_len(c.model) + to_integer(n);
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
fail: reads a resource binder's model and also the C variable `n`
```
