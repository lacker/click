# deleting the binder introduction is rejected

The same proof as `quantifier_intro_nested_connectives.md` with the universal's
`intro()` deleted. The remaining script starts by introducing the antecedent of
a goal that is still a `forall`, so the proof is rejected rather than silently
closed by a quantifier search inside `normalize`.

```c filename=quantifier_intro_nested_connectives_rejects_missing_intro.c
int32 quantifier_intro_nested_connectives_rejects_missing_intro(int32 n) {
    return n;
}
```

```click
verifying "quantifier_intro_nested_connectives_rejects_missing_intro.c";

theorem nested_universal_body(n: int32) {
    ensures forall (k: int32) {
        0 <= k and k < n implies (0 <= k and (k < n or k == n))
    } by {
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
fail: extract
```
