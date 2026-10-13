# `have P by auto` proves a linear bound with the solver

On a stated fact, `auto` runs no C. It refutes the fact's integer negation
from the facts connected to it, and applies the result as one checked
`arithmetic_certificate`. Here the bound needs three premises chained
through a scaled one, which no listed premise states directly.

```click
theorem solver_chains_bounds(i: Integer, n: Integer, total: Integer) {
    requires i < n;
    requires n <= 1000;
    requires total <= 255 * i;
    ensures total <= 255000 by {
        have total <= 255000 by auto;
        assumption();
    }
}
```

```expect
pass
```
