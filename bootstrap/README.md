# Bootstrap Layout

The `bootstrap/` tree holds self-hosted Click programs that exercise the
kernel.

- `base/`
  Shared bootstrap terms.
- `data/`
  First typed library terms defined on top of the token core.
- `named_core/`
  Programs for the current named-variable core.
- `token_core/`
  Programs for the more explicit typed token-core experiments.

Current files:

- `base/fix.cl`
  A fixed-point combinator used by the recursive checkers.
- `base/assoc.cl`
  A recursive lookup function for simple association lists.
- `base/equal.cl`
  A recursive structural equality function over quoted Click data.
- `named_core/wf.cl`
  A well-formedness checker for quoted terms in the current named core.
- `named_core/eval.cl`
  A self-hosted evaluator for the current named core.
- `token_core/wf.cl`
  A well-formedness checker for quoted token-core terms.
- `token_core/eval_env.cl`
  A self-hosted evaluator for closed quoted token-core terms, using explicit
  closure/environment values.
- `token_core/subst.cl`
  A capture-avoiding substitution helper for the token-core syntax.
- `token_core/typecheck.cl`
  A self-hosted typechecker for the typed token-core experiment.
- `data/bool_type.cl`
  A Church-encoded `Bool` type.
- `data/bool_true.cl`
  The `true` inhabitant of the encoded `Bool`.
- `data/bool_false.cl`
  The `false` inhabitant of the encoded `Bool`.
- `data/bool_if.cl`
  A small eliminator for the encoded `Bool`.

The current `Bool` probe already exposed one important lesson: evaluation works
more cleanly with explicit closure/environment values than with syntax
rewriting, because it avoids alpha-renaming problems during beta-reduction.

`tests/bootstrap.rs` loads these files directly and supplies the concrete test
inputs from Rust.
