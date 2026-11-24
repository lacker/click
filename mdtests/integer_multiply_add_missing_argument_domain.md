# Distributivity arguments retain truncation domains even in a zero product

```click
import click::integer;

theorem erased_domain(n: Integer, d: Integer) {
    ensures 0 == 0 by {
        apply(integer::multiply_add(truncating_quotient(n, d), 0, 0));
        close();
    }
}
```

```expect
fail: has an unproved obligation
```
