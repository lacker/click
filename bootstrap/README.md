# Bootstrap Layout

The `bootstrap/` tree holds self-hosted Click programs that exercise the
kernel.

- `base/`
  Shared bootstrap terms.
- `named_core/`
  Programs for the current named-variable core.
- `token_core/`
  Programs for the more explicit typed token-core experiments.

Current files:

- `base/fix.cl`
  A fixed-point combinator used by the recursive checkers.
- `named_core/wf.cl`
  A well-formedness checker for quoted terms in the current named core.
- `token_core/wf.cl`
  A well-formedness checker for quoted token-core terms.

`tests/bootstrap.rs` loads these files directly and supplies the concrete test
inputs from Rust.
