# a loop measure has to have an order

`decreases c.model;` names the binder's model itself, a `Chain`. A spec enum
has no order a ranking member can compare, so the measure is refused where it
is declared. The two spellings that do rank by the structure are the binder,
`decreases c;`, and a function of its model into `Integer` or `Nat`.

```c filename=loop_decreases_rejects_an_unordered_model.c
void countdown(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
}
```

```click
verifying "loop_decreases_rejects_an_unordered_model.c";

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
        decreases c.model;
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
fail: has type `Chain`, which has no order a termination measure can rank
```
