# Propositions

A proposition is a claim that can be true or false.

Contracts are built from propositions:

```click
requires x >= 0;
ensures result == x + 1 by auto;
```

The expressions `x >= 0` and `result == x + 1` are propositions.

## Propositions Are Not C Expressions

Click lets you write C-like fragments inside specs:

```click
result == x + 1
p[k] == old(p[k])
```

But the surrounding logic is Click, not C. Click proposition connectives are
words:

```click
a and b
a or b
not a
a implies b
```

Do not write C logical operators such as `&&`, `||`, or `!` in propositions.

## Quantifiers

Click supports universal and existential claims:

```click
forall (int32 k) {
    0 <= k and k < n implies p[k] == old(p[k])
}

exists (int32 k) {
    0 <= k and k < n and p[k] == value
}
```

Read `forall` as "for every" and `exists` as "there is some".

Quantifiers are powerful, but they often need explicit proof structure. For
ranges of memory, range forms are usually easier to prove.

## Range Propositions

Click has range forms for array-shaped facts:

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

## Old Values

`old(expr)` means the value of `expr` in the function-entry state:

```click
ensures p[0] == old(p[0]) by auto;
```

Old values are central for memory proofs. They let a postcondition compare the
final state with the state at function entry.
