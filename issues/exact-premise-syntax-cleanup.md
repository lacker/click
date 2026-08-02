# Remove redundancy from exact-premise tactics

## Problem

Click's smart/simple tactic boundary is now coherent, but the simple
exact-premise surface repeats information already fixed by the surrounding
syntax. The most conspicuous form is:

```click
have P by {
    derive(P) using {
        fact Q;
    }
}
```

`have` establishes `P` as the current nested goal, and `derive` already checks
that its target is that current goal. Repeating `P` does not make the
certificate more exact. Likewise, every item in a tactic `using` block is
currently required to be a pure proposition, so repeating `fact` on every line
adds no information. Finally, exact `step using` is the only paired tactic that
drops the operation's otherwise canonical parentheses.

This verbosity matters because expanded certificates are ordinary maintained
Surface Click, not a private output format. Exactness should mean that the
premises are listed explicitly; it does not require repeating their type or the
current goal.

## Canonical syntax

Adopt this spelling:

```click
have P by {
    derive using {
        Q;
        R;
    }
}

step() using {
    Q;
}

summarize(loop(0)) using {
    Q;
}

frame() using {
    Q;
}

apply(theorem_name(x)) using {
    Q;
}

transport(P, at(checkpoint.entry, P)) using {
    Q;
}
```

The rule is uniform:

- A bare paired operation is smart and selects relevant premises from context.
- The same operation followed by `using { ... }` is simple and uses exactly
  the listed pure premises.
- A `using` block is a homogeneous list of propositions, so its entries do not
  carry a `fact` prefix.
- `derive` closes the current pure proposition goal, so it does not accept a
  separate target.

An empty `using {}` block remains valid for operations whose exact rule needs
no pure premises. `derive using {}` remains invalid; a context-free goal uses
`normalize()`.

## Keep `have` and `derive` separate

Do not replace the composition with special syntax such as
`have P using { ... }`. `have` is a control operation: it creates a nested pure
goal and adds the completed proposition to the surrounding context. `derive`
is one deterministic way to close the current atomic goal. Keeping those roles
separate lets a `have` proof continue to use `simp`, `apply`, logical tactics,
or a multi-step script without accumulating proof-method-specific forms of
`have`.

Do not permit direct `derive` in a grouped execution proof merely as a way to
add a fact. That would give the same spelling two meanings: close the current
pure goal in one context, but mutate the ambient fact context in another.

## Heterogeneous blocks

Keep assertion-kind keywords in `reach` interfaces:

```click
reach(checkpoint.exit)
ensuring {
    fact P;
    owns buffer[0..n];
    views shared_state(token);
}
by {
    // ...
}
```

Unlike `using`, an `ensuring` block is heterogeneous. `fact`, `owns`, and
`views` communicate real information there and should remain.

## Migration and diagnostics

- Migrate repository examples, mdtests, standard-library proofs, and docs to
  `derive using`, proposition-only `using` entries, and `step() using`.
- Make every certificate printer emit only the canonical forms.
- Reject `derive(P) using`, `fact P;` inside a tactic `using` block, and
  `step using` with focused messages showing the replacement.
- Do not retain aliases indefinitely. Click should continue to have one
  canonical spelling for each operation.
- Preserve the existing smart/simple classification and profiling labels. This
  issue changes syntax, not tactic semantics or performance accounting.

## Documentation

Update at least:

- `docs/proof-tactics.md`;
- `docs/basic/proofs-and-proof-scripts.md`;
- `docs/proof-workflow.md`;
- examples and their READMEs where exact certificates are discussed; and
- parser, expansion, profile, and audit diagnostics that display tactic text.

## Acceptance criteria

- `derive using { P; ... }` closes exactly the current pure proposition goal
  from exactly the listed premises.
- There is no accepted or printed `derive(target)` surface form.
- All paired exact operations use the same call-shaped operation followed by
  `using { ... }`, including `step() using`.
- Tactic `using` blocks accept bare proposition entries and do not accept the
  redundant `fact` prefix.
- `reach ... ensuring` continues to require `fact`, `owns`, or `views` on each
  assertion.
- Empty exact-premise blocks retain their current behavior; empty `derive`
  remains a focused error directing the user to `normalize()`.
- Expansion emits certificates accepted by the ordinary parser, and replay
  checks the same exact premises as before.
- Profile and audit continue to classify the resulting leaves as simple.
- The default test suite passes.
