# a `void` function's `ensures` compares an Integer function with a numeral

An `ensures` that compares a mathematical `Integer` Click function with a
numeral is what every Integer-carrying contract clause looks like, and it was
accepted everywhere except in a `void` function's `ensures`, where it was
refused with `sequence equality requires a sequence on both sides`. Contract
validation reached for the C-only validator exactly when the return type was
`Void`, and that validator has no Integer context, so it typed the numeral as
an int32 and the call as neither. The return type is not supposed to decide
which propositions a contract may state, and both branches now validate the
same way.

```c filename=void_ensures_compares_an_integer_function.c
void probe(int32 n) {
    return;
}
```

```click
verifying "void_ensures_compares_an_integer_function.c";

function widened(k: int32) -> Integer {
    to_integer(k) - to_integer(k)
}

void probe(int32 n) {
    ensures widened(n) == 0;
} by {
    execute();
    unfold(widened(n));
    simp();
}
```

```expect
pass
```
