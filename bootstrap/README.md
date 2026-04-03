# Bootstrap Layout

The `bootstrap/` tree holds self-hosted Click programs that exercise the
kernel.

- `base/`
  Shared bootstrap terms.
- `data/`
  First typed library terms defined on top of the token core.
- `proofs/`
  First proposition and proof terms on top of the token core.
- `token_core/`
  Programs for the more explicit typed token-core experiments.

Current files:

- `base/fix.cl`
  A fixed-point combinator used by the recursive checkers.
- `base/assoc.cl`
  A recursive lookup function for simple association lists.
- `base/structural_equal.cl`
  A recursive structural equality function over quoted Click data.
- `token_core/alpha_eq.cl`
  A recursive alpha-equivalence checker for quoted token-core terms.
- `token_core/whnf.cl`
  A small weak-head reducer for quoted token-core terms.
- `token_core/wf.cl`
  A well-formedness checker for quoted token-core terms.
- `token_core/eval_env.cl`
  A self-hosted evaluator for closed quoted token-core terms, using explicit
  closure/environment values.
- `token_core/infer.cl`
  A self-hosted type inferencer for the typed token-core experiment.
- `token_core/subst.cl`
  A capture-avoiding substitution helper for the token-core syntax.
- `token_core/typecheck.cl`
  A goal-directed typechecker for the typed token-core experiment. It checks a
  quoted term against an expected type by calling `infer.cl`, then comparing
  the inferred and expected types up to weak-head computation and
  alpha-equivalence.
- `data/bool_type.cl`
  A Church-encoded `Bool` type.
- `data/bool_true.cl`
  The `true` inhabitant of the encoded `Bool`.
- `data/bool_false.cl`
  The `false` inhabitant of the encoded `Bool`.
- `data/bool_if.cl`
  A small eliminator for the encoded `Bool`.
- `proofs/eq.cl`
  A Leibniz-style equality proposition.
- `proofs/refl.cl`
  Reflexivity for the encoded equality proposition.

The current `Bool` probe already exposed one important lesson: evaluation works
more cleanly with explicit closure/environment values than with syntax
rewriting, because it avoids alpha-renaming problems during beta-reduction.

The first proof probe is now in place too: the token core can already host an
encoded equality proposition and a `refl` proof term for it.

`tests/bootstrap.rs` loads these files directly and supplies the concrete test
inputs from Rust.
