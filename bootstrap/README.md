# Bootstrap Layout

The `bootstrap/` tree is archival.

These programs were written against older Click experiments, especially the
quote/list-based kernel. They are still useful as records of language-design
work, but they do not describe the current kernel surface.

Current structure:

- `base/`
  Shared historical helpers.
- `data/`
  Early typed library experiments on top of the old token core.
- `proofs/`
  Early proposition and proof experiments on top of the old token core.
- `token_core/`
  Historical typed kernel experiments written in Click itself.

File guide:

- `base/fix.cl`
  A fixed-point combinator used by the recursive experiments.
- `base/assoc.cl`
  A lookup helper for simple association lists.
- `base/structural_equal.cl`
  Structural equality over quoted Click data.
- `token_core/alpha_eq.cl`
  Alpha-equivalence for quoted token-core terms.
- `token_core/whnf.cl`
  Weak-head reduction for quoted token-core terms.
- `token_core/wf.cl`
  Well-formedness checking for quoted token-core terms.
- `token_core/eval_env.cl`
  A self-hosted evaluator for closed quoted token-core terms, using explicit
  function/environment values.
- `token_core/infer.cl`
  A self-hosted type inferencer for the typed token-core experiment.
- `token_core/subst.cl`
  A capture-avoiding substitution helper for the token-core syntax.
- `token_core/typecheck.cl`
  A goal-directed typechecker for the typed token-core experiment.
- `data/bool_type.cl`
  A Church-encoded `Bool` type.
- `data/bool_true.cl`
  The `true` inhabitant of that encoded `Bool`.
- `data/bool_false.cl`
  The `false` inhabitant of that encoded `Bool`.
- `data/bool_if.cl`
  An eliminator for the encoded `Bool`.
- `proofs/eq.cl`
  A Leibniz-style equality proposition.
- `proofs/refl.cl`
  Reflexivity for the encoded equality proposition.
- `proofs/transport.cl`
  Proof transport for the encoded equality proposition.
- `proofs/sym.cl`
  Symmetry for the encoded equality proposition.
- `proofs/trans.cl`
  Transitivity for the encoded equality proposition.

The main historical lesson from this tree is still useful: once binders enter
the language, the representation of code matters. The older named-syntax
experiments found explicit environments simpler than naive named substitution.
The current kernel addresses that differently by lowering surface syntax into
de Bruijn-based `Term`s before evaluation.
