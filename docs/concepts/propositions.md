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

## Pointer disequality

Two pointers are decided different when the context already says so about the
pointers themselves, in one of two ways.

The first is null-ness. One pointer is null and the other is not, so they
cannot be the same pointer:

<!-- verified-example: mdtests/pointer_disequality_from_null.md -->
```click
requires p == 0;
requires q != 0;
```

With those, the C test `if (p == q)` is decided false before it splits. The
null side may be read out of an owned cell (`requires node->left == 0;`)
rather than named by a parameter; a loaded pointer is a pointer like any
other. `mdtests/rb_ctx_change_child.md`'s right-child wrapper is the same step on the
unchanged Linux `__rb_change_child`: the right-child frame's empty left
sibling makes `parent->rb_left` null, the caller's child exists, and the
helper's inner `parent->rb_left == old` test is decided with no requirement
about `parent->rb_left`.

The second is separate ownership. Two objects owned at once are separate, and
two ranges that both hold their own first element cannot be separate at the
same address, so their pointers differ:

<!-- verified-example: mdtests/pointer_disequality_from_separation.md -->
```click
owns a->left;
owns b->left;
```

Nothing needs to be stated: the composition of those two `owns` clauses
already projects the separation. This route needs the two objects to be
separate in *one* composition; ownership that reaches a frontier as two
independent compositions states no separation between them.

Neither rule ever decides a comparison true, and neither searches. When
nothing settles one of the two pointers the comparison stays undecided,
execution keeps both paths, and the proof has to handle both — see
`mdtests/pointer_disequality_rejects_undecided.md`.

## Old values

`old(expr)` means the value of `expr` in the function-entry state:

<!-- verified-example: mdtests/click_proposition_logic.md -->
```click
ensures p[0] == old(p[0]) by auto;
```

Old values are central for memory proofs. They let a postcondition compare the
final state with the state at function entry.
