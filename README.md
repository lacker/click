# click

`click` is a very small Lisp-y kernel implemented in Rust.

The current prototype supports:

- top-level `def` declarations
- `quote`
- `object`
- `get`
- `with`
- `has`
- `if`
- `atom`
- `atom_eq`
- `car`
- `cdr`
- `cons`
- `var`
- `app`
- `lambda`
- `nil`
- `true`
- `false`

This version uses explicit named variables. Executable list forms are tagged by
their first atom, variable references are written as `(var name)`, and function
application is written as `(app f a)`.

## Semantics

- Ordinary atoms do not self-evaluate. Only `nil`, `true`, and `false` do.
- Top-level `(def name expr)` declarations extend the context for later forms.
- `quote` turns code into ordinary list data: `(quote (lambda x (var x)))`.
- `object` is an immutable named map. `with` returns an updated object, `get`
  reads a key, and `has` checks for a key.
- `lambda` has the form `(lambda x body)` and captures the current lexical object environment.
- Rebinding a name that is already in scope is an error.
- Closures are an internal evaluator detail. Evaluating a lambda prints `#<closure>`.
- `atom` returns `true` for atoms, booleans, and `nil`.
- `atom_eq` only accepts atom arguments.
- `if` treats `false` and `nil` as falsey. Everything else is truthy.
- `car` and `cdr` are partial: applying them to `nil` is an error.
- `cons` builds pairs. Proper lists print as `(a b c)`. Improper lists print as `(a . b)`.

## Usage

Run an expression directly:

```bash
cargo run -- -e "(app (lambda x (var x)) 'a)"
```

Run a file:

```bash
cargo run -- examples/list.cl
```

Pipe a program on stdin:

```bash
printf "(car (quote (a b c)))\n" | cargo run --
```

Install the binary and use it as a shebang interpreter:

```bash
cargo install --path .
chmod +x examples/list.cl
./examples/list.cl
```

`click` ignores a leading `#!...` line in source files.

Top-level definitions work across later forms in the same source:

```lisp
(def id (lambda x (var x)))
(app (var id) 'a)
```

## Code As Data

Quoted code is ordinary data, so Click programs can inspect Click programs with
the usual list operations. For a tiny example:

- [`examples/code_shape.cl`](examples/code_shape.cl) extracts the binder from a quoted lambda.

The kernel also has primitive named objects for environment-like structure:

```lisp
(with (object) 'foo 'bar)
(get (with (object) 'foo 'bar) 'foo)
```

The larger self-hosted experiments now live in:

- [`bootstrap/README.md`](bootstrap/README.md)
- [`bootstrap/base/fix.cl`](bootstrap/base/fix.cl)
- [`bootstrap/base/assoc.cl`](bootstrap/base/assoc.cl)
- [`bootstrap/base/structural_equal.cl`](bootstrap/base/structural_equal.cl)
- [`bootstrap/token_core/alpha_eq.cl`](bootstrap/token_core/alpha_eq.cl)
- [`bootstrap/token_core/whnf.cl`](bootstrap/token_core/whnf.cl)
- [`bootstrap/data/bool_type.cl`](bootstrap/data/bool_type.cl)
- [`bootstrap/data/bool_true.cl`](bootstrap/data/bool_true.cl)
- [`bootstrap/data/bool_false.cl`](bootstrap/data/bool_false.cl)
- [`bootstrap/data/bool_if.cl`](bootstrap/data/bool_if.cl)
- [`bootstrap/proofs/eq.cl`](bootstrap/proofs/eq.cl)
- [`bootstrap/proofs/refl.cl`](bootstrap/proofs/refl.cl)
- [`bootstrap/proofs/transport.cl`](bootstrap/proofs/transport.cl)
- [`bootstrap/proofs/sym.cl`](bootstrap/proofs/sym.cl)
- [`bootstrap/proofs/trans.cl`](bootstrap/proofs/trans.cl)
- [`bootstrap/token_core/eval_env.cl`](bootstrap/token_core/eval_env.cl)
- [`bootstrap/token_core/infer.cl`](bootstrap/token_core/infer.cl)
- [`bootstrap/token_core/subst.cl`](bootstrap/token_core/subst.cl)
- [`bootstrap/token_core/typecheck.cl`](bootstrap/token_core/typecheck.cl)
- [`bootstrap/token_core/wf.cl`](bootstrap/token_core/wf.cl)

[`tests/bootstrap.rs`](tests/bootstrap.rs) loads those files and checks:

- a recursive assoc-list lookup helper
- a recursive structural equality helper over quoted data
- an alpha-equivalence helper for quoted token-core terms
- a weak-head reducer for quoted token-core terms
- a first typed `Bool` layer built on the token core
- first proof toolkit terms: an encoded equality proposition, `refl`,
  transport, symmetry, and transitivity
- a recursive token-core checker for quoted terms like `(lambda x type (var x))`
- a token-core evaluator for closed quoted terms built around explicit
  closure/environment values
- a self-hosted token-core inferencer for quoted terms like
  `(lambda x type (var x))`
- a goal-directed token-core `typecheck` that checks a quoted term against an
  expected type, using weak-head computation plus alpha-equivalence for
  conversion

The first typed `Bool` probe already found the important design lesson:
evaluation works more cleanly with explicit closure/environment values than
with syntax rewriting, because it avoids alpha-renaming problems during
beta-reduction.

The first proof toolkit is now in place too: the token core can already host a
Leibniz-style equality type, `refl`, and basic equality reasoning combinators.
