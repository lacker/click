# Propositions

Typed logical binders use Click's `name: type` convention, as in
`forall (k: int32)` and `exists (item: uint8)`. The `type name` convention is
reserved for attached C function signatures.

A proposition is a claim that can be true or false.

Contracts are built from propositions:

<!-- verified-example: mdtests/click_proposition_logic.md -->
```click
requires x >= 0;
ensures result == x + 1 by auto;
```

The expressions `x >= 0` and `result == x + 1` are propositions.

## Propositions are not C expressions

Click lets you write C-like fragments inside specs:

<!-- verified-example: mdtests/click_proposition_logic.md -->
```click
result == x + 1
p[k] == old(p[k])
```

But the surrounding logic is Click, not C. Click proposition connectives are
words:

<!-- verified-example: mdtests/click_proposition_logic.md -->
```click
a and b
a or b
not a
a implies b
```

Do not write C logical operators such as `&&`, `||`, or `!` in propositions.

## Quantifiers

Click supports universal and existential claims:

<!-- verified-example: mdtests/click_proposition_logic.md -->
```click
forall (k: int32) {
    0 <= k and k < n implies p[k] == old(p[k])
}

exists (k: int32) {
    0 <= k and k < n and p[k] == value
}
```

Read `forall` as "for every" and `exists` as "there is some".

Quantifiers are powerful, but they often need explicit proof structure. For
ranges of memory, range forms are usually easier to prove.

## Range propositions

Click has range forms for array-shaped facts:

<!-- verified-example: mdtests/click_proposition_logic.md -->
```click
(0..n).all(|k| {
    p[k] == 0
})

(0..n).any(|k| {
    p[k] == value
})
```

The range `0..n` is half-open: it includes `0` and excludes `n`.

These forms are useful because Click can lower the body under the fact that
`k` is in the range. That matters for memory safety: a read such as `p[k]` is
safe only when Click knows `k` is within a loadable range.

## Model payloads

A resource model can carry C values as constructor payloads, including
pointers. Those payloads are ordinary values of their C type, so a proposition
may mix them freely with C expressions:

<!-- verified-example: mdtests/model_identity_pointer_payload.md -->
```click
have p == identity by { simp(); }
```

Here `identity` is the `struct cell*` payload a proof `match` bound, and `p` is
a C parameter. The resource states `fact p == identity` in that arm, which is
what makes the address the C compares and the identity the model records the
same pointer. Pointer payloads stay pointers: nothing converts them to
integers, and they carry no ownership of their own.

The payload bindings a proof `match` introduces stay in scope for the whole
arm, including inside a `branch` arm, a proof-level `if` arm, and the body of
a `have` — see `mdtests/match_bindings_in_branch_arm.md`.

## Old values

`old(expr)` means the value of `expr` in the function-entry state:

<!-- verified-example: mdtests/click_proposition_logic.md -->
```click
ensures p[0] == old(p[0]) by auto;
```

Old values are central for memory proofs. They let a postcondition compare the
final state with the state at function entry.
