# A contract script ending in `simp` does not search like `auto`

An explicit `simp()` closes a contract with `simp` alone. The claim needs
a requirement as a rewrite from right to left, which `simp` does not search
for, so
this proof is refused; without the closer it verifies
(`a_contract_script_without_a_closer_ends_with_auto.md`).

```c filename=a_contract_script_ending_in_simp_does_not_search.c
void touch(int32 n) {
}
```

```click
verifying "a_contract_script_ending_in_simp_does_not_search.c";

spec enum Walk { At(Integer, Walk), Done }

function black(w: Walk) -> int32 decreases w {
    match w { Walk::At(wd, rest) => black(rest), Walk::Done => 1 }
}

resource token(k: int32) {
    field model: Walk;
}

void touch(int32 n) {
    owns c: token(n);
    requires c.model == Walk::At(to_integer(n), Walk::Done);
    requires black(c.model) == 1;
    ensures black(Walk::At(to_integer(n), Walk::Done)) == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: simp
```
