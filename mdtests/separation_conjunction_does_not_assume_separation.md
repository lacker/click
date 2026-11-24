# Naming a conjunction does not supply its operands' separation or ownership

```click
import click::separation;
theorem no_permission(A: Resource, B: Resource) {
    ensures separate(A, B) by {
        apply(separation::contains_left(A, B));
        apply(separation::contains_right(A, B));
        close();
    }
}
```

```expect
fail: could not establish `separate(A, B)`
```
