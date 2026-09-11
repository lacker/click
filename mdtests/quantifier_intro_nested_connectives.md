# a universal with nested connectives is introduced, not normalized

`normalize` closes a leaf, not a quantifier. A universal whose body nests an
implication, a conjunction, and a disjunction is proved by introducing the
binder and the antecedent and then spelling each connective: `both` for the
conjunction and a proved arm followed by `left` for the disjunction.

The range here is symbolic, so `enumerate` does not apply and the binder must
be introduced. `quantifier_intro_nested_connectives_rejects_missing_intro.md`
is the same proof with the binder introduction deleted.

```c filename=quantifier_intro_nested_connectives.c
int32 quantifier_intro_nested_connectives(int32 n) {
    return n;
}
```

```click
verifying "quantifier_intro_nested_connectives.c";

theorem nested_universal_body(n: int32) {
    ensures forall (k: int32) {
        0 <= k and k < n implies (0 <= k and (k < n or k == n))
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < n);
        both {
            assumption();
        } and {
            have k < n by { assumption(); }
            left();
        }
    }
}
```

```expect
pass
```
