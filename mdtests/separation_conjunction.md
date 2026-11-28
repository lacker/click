# Separating conjunction is a descriptor, with explicit library laws

```click
import click::separation;
theorem frame(A: Resource, B: Resource, C: Resource, E: Resource) {
    requires separate(A, C);
    requires separate(B, C);
    requires contains(A * B, E);
    ensures separate(E, C) by {
        apply(separation::separate_star(A, B, C));
        apply(separation::contains_refl(C));
        apply(separation::separate_restrict(A * B, C, E, C));
        close();
    }
}
theorem components(A: Resource, B: Resource, C: Resource) {
    ensures contains((A * B) * C, B) by {
        apply(separation::contains_left(A * B, C));
        apply(separation::contains_right(A, B));
        apply(separation::contains_trans((A * B) * C, A * B, B));
        close();
    }
}
theorem empty(A: Resource) {
    ensures separate(A, separation::emp) by {
        apply(separation::separate_emp(A));
        apply(separation::separate_symm(separation::emp, A));
        close();
    }
}
```

```expect
pass
```
