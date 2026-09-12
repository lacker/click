# Preserve lexical aliases under quantifier binders

P1: clause-level `let` expansion captures free variables and accepts false
theorems. Reproduced at `3ad0d2e1` with explicit simple tactics.

## Violated invariant

A lexical alias denotes its initializer in the environment where it was
defined. Introducing or alpha-renaming a later binder must not change the
alias's value or change a false proposition into a true one.

`apply_contract_let_expressions_to_proposition` in
`src/surface/lowering/contract_substitution.rs` removes aliases whose names
equal a quantifier binder, then applies the remaining aliases inside its
body. It does not freshen binders that occur free in alias initializers.
`apply_contract_lets_to_expression` substitutes untyped aliases and inserts
retained typed aliases inside the body; both paths can capture variables.
The general substitution route already has
`prepare_click_proposition_binding_body`, but this special alias-expansion
route bypasses its capture avoidance.

## Small reproduction

Save this as `capture.click`; no C input is needed:

```click
theorem wrong(x: int32) {
    let saved = x;
    ensures forall (x: int32) { saved == x } by {
        intro();
        normalize();
    }
}
```

`click verify capture.click` exits 0. For outer `x = 0`, `saved` must remain
0, while the inner universal quantifier includes 1, so the theorem is false.
Substitution instead changes the body into the tautology `x == x`.

Rename only the inner binder and its reference to `z`:

```click
ensures forall (z: int32) { saved == z } by {
    intro();
    normalize();
}
```

The alpha-equivalent theorem now correctly fails at `normalize`. Replacing
the outer and inner types with `Integer` and writing
`let saved: Integer = x;` reproduces the same unsound acceptance.

The existential path also accepts an impossible claim:

```click
theorem wrong(x: Integer) {
    requires x == 0;
    let saved: Integer = x;
    ensures exists (x: Integer) { saved == 1 } by {
        witness(x = 1);
        normalize();
    }
}
```

This exits 0 even though `saved` is fixed at 0 by the outer requirement.

## Acceptance criteria

- Reject these false-theorem examples and their alpha-renamed forms;
  retain true lexical-alias properties under both unrelated and shadowing
  binders.
- Use binder identities or capture-avoiding substitution to preserve
  definition-time free variables. Do not rename the reproduction or ban
  otherwise legal shadowing to hide the defect.
- Cover `forall`, `exists`, range `.all`/`.any`, nested binders, chained
  aliases, typed and untyped aliases, and `let ... where` interactions.
  The range substitution branches use the same pattern and require audit.
- Ordinary verification and expanded explicit proofs must certify the same
  source proposition. Protect any representation change with deterministic
  scaling regressions that satisfy the verification-efficiency contract.
- `scripts/check.sh` passes.
