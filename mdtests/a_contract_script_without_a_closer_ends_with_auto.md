# A contract script without a closer ends with `auto`

A whole-contract proof script that stops before closing every claim ends
with `auto`, as an omitted proof does: `simp` on each open claim, then the
rest of `auto`'s search. Here the claim needs the requirement
`c.model == Walk::At(to_integer(n), Walk::Done)` as a rewrite from right to
left, which `auto` finds and `simp` does not (`a_contract_script_ending_in_simp_does_not_search.md`). `click expand`
writes the closer out as checked steps at the end of the script.

```c filename=a_contract_script_without_a_closer_ends_with_auto.c
void touch(int32 n) {
}
```

```click
verifying "a_contract_script_without_a_closer_ends_with_auto.c";

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
}
```

```expect
pass
```
